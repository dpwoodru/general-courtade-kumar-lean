import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0414
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

theorem reflection_log_1_neg : (98431871 / 500000000) ≤ -Real.log (2560 / 3117) ∧
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


theorem reflection_log_1 : Bounds (98431871 / 500000000) (196863743 / 1000000000) (Real.log (3117 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3117 / 2560) = -Real.log (2560 / 3117) := by
    rw [show ((3117 / 2560) : ℝ) = ((2560 / 3117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (245361201 / 1000000000) ≤ -Real.log (2003 / 2560) ∧
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


theorem reflection_log_2 : Bounds (-122680601 / 500000000) (-245361201 / 1000000000) (Real.log (2003 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (196623097 / 1000000000) ≤ -Real.log (2048 / 2493) ∧
    -Real.log (2048 / 2493) ≤ (98311549 / 500000000) := by
  have h := checkLog_sound (w := (445 / 4541)) (n := 12)
    (lo := (196623097 / 1000000000)) (hi := (98311549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2493 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2493 / 2048) = 1/(2048 / 2493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (196623097 / 1000000000) (98311549 / 500000000) (Real.log (2493 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2493 / 2048) = -Real.log (2048 / 2493) := by
    rw [show ((2493 / 2048) : ℝ) = ((2048 / 2493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (244986833 / 1000000000) ≤ -Real.log (1603 / 2048) ∧
    -Real.log (1603 / 2048) ≤ (122493417 / 500000000) := by
  have h := checkLog_sound (w := (445 / 3651)) (n := 12)
    (lo := (244986833 / 1000000000)) (hi := (122493417 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1603) = 1/(1603 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-122493417 / 500000000) (-244986833 / 1000000000) (Real.log (1603 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (2822451 / 7812500) ≤ -Real.log (1280 / 1837) ∧
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


theorem reflection_log_5 : Bounds (2822451 / 7812500) (361273729 / 1000000000) (Real.log (1837 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1837 / 1280) = -Real.log (1280 / 1837) := by
    rw [show ((1837 / 1280) : ℝ) = ((1280 / 1837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (285603067 / 500000000) ≤ -Real.log (723 / 1280) ∧
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


theorem reflection_log_6 : Bounds (-114241227 / 200000000) (-285603067 / 500000000) (Real.log (723 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (36086537 / 100000000) ≤ -Real.log (1024 / 1469) ∧
    -Real.log (1024 / 1469) ≤ (360865371 / 1000000000) := by
  have h := checkLog_sound (w := (445 / 2493)) (n := 12)
    (lo := (36086537 / 100000000)) (hi := (360865371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1469 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1469 / 1024) = 1/(1024 / 1469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (36086537 / 100000000) (360865371 / 1000000000) (Real.log (1469 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1469 / 1024) = -Real.log (1024 / 1469) := by
    rw [show ((1469 / 1024) : ℝ) = ((1024 / 1469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (35635583 / 62500000) ≤ -Real.log (579 / 1024) ∧
    -Real.log (579 / 1024) ≤ (570169329 / 1000000000) := by
  have h := checkLog_sound (w := (445 / 1603)) (n := 12)
    (lo := (35635583 / 62500000)) (hi := (570169329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 579) = 1/(579 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-570169329 / 1000000000) (-35635583 / 62500000) (Real.log (579 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (269963013 / 1000000000) ≤ -Real.log (250000 / 327479) ∧
    -Real.log (250000 / 327479) ≤ (134981507 / 500000000) := by
  have h := checkLog_sound (w := (77479 / 577479)) (n := 12)
    (lo := (269963013 / 1000000000)) (hi := (134981507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((327479 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(327479 / 250000) = 1/(250000 / 327479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (269963013 / 1000000000) (134981507 / 500000000) (Real.log (327479 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (327479 / 250000) = -Real.log (250000 / 327479) := by
    rw [show ((327479 / 250000) : ℝ) = ((250000 / 327479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (370941949 / 1000000000) ≤ -Real.log (172521 / 250000) ∧
    -Real.log (172521 / 250000) ≤ (7418839 / 20000000) := by
  have h := checkLog_sound (w := (77479 / 422521)) (n := 12)
    (lo := (370941949 / 1000000000)) (hi := (7418839 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 172521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 172521) = 1/(172521 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-7418839 / 20000000) (-370941949 / 1000000000) (Real.log (172521 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (54057787 / 200000000) ≤ -Real.log (1000000 / 1310343) ∧
    -Real.log (1000000 / 1310343) ≤ (33786117 / 125000000) := by
  have h := checkLog_sound (w := (310343 / 2310343)) (n := 12)
    (lo := (54057787 / 200000000)) (hi := (33786117 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1310343 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1310343 / 1000000) = 1/(1000000 / 1310343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (54057787 / 200000000) (33786117 / 125000000) (Real.log (1310343 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1310343 / 1000000) = -Real.log (1000000 / 1310343) := by
    rw [show ((1310343 / 1000000) : ℝ) = ((1000000 / 1310343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (185780453 / 500000000) ≤ -Real.log (689657 / 1000000) ∧
    -Real.log (689657 / 1000000) ≤ (371560907 / 1000000000) := by
  have h := checkLog_sound (w := (310343 / 1689657)) (n := 12)
    (lo := (185780453 / 500000000)) (hi := (371560907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 689657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 689657) = 1/(689657 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-371560907 / 1000000000) (-185780453 / 500000000) (Real.log (689657 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (2538087 / 12500000) ≤ -Real.log (100000 / 122513) ∧
    -Real.log (100000 / 122513) ≤ (203046961 / 1000000000) := by
  have h := checkLog_sound (w := (22513 / 222513)) (n := 12)
    (lo := (2538087 / 12500000)) (hi := (203046961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122513 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122513 / 100000) = 1/(100000 / 122513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (2538087 / 12500000) (203046961 / 1000000000) (Real.log (122513 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (122513 / 100000) = -Real.log (100000 / 122513) := by
    rw [show ((122513 / 100000) : ℝ) = ((100000 / 122513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (51012001 / 200000000) ≤ -Real.log (77487 / 100000) ∧
    -Real.log (77487 / 100000) ≤ (127530003 / 500000000) := by
  have h := checkLog_sound (w := (22513 / 177487)) (n := 12)
    (lo := (51012001 / 200000000)) (hi := (127530003 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 77487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 77487) = 1/(77487 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-127530003 / 500000000) (-51012001 / 200000000) (Real.log (77487 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (40662767 / 200000000) ≤ -Real.log (1000000 / 1225457) ∧
    -Real.log (1000000 / 1225457) ≤ (50828459 / 250000000) := by
  have h := checkLog_sound (w := (225457 / 2225457)) (n := 12)
    (lo := (40662767 / 200000000)) (hi := (50828459 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1225457 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1225457 / 1000000) = 1/(1000000 / 1225457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (40662767 / 200000000) (50828459 / 250000000) (Real.log (1225457 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1225457 / 1000000) = -Real.log (1000000 / 1225457) := by
    rw [show ((1225457 / 1000000) : ℝ) = ((1000000 / 1225457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2554821 / 10000000) ≤ -Real.log (774543 / 1000000) ∧
    -Real.log (774543 / 1000000) ≤ (255482101 / 1000000000) := by
  have h := checkLog_sound (w := (225457 / 1774543)) (n := 12)
    (lo := (2554821 / 10000000)) (hi := (255482101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 774543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 774543) = 1/(774543 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-255482101 / 1000000000) (-2554821 / 10000000) (Real.log (774543 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (320452481 / 500000000) ≤ -Real.log (3906250000 / 7414835549) ∧
    -Real.log (3906250000 / 7414835549) ≤ (640904963 / 1000000000) := by
  have h := checkLog_sound (w := (3508585549 / 11321085549)) (n := 12)
    (lo := (320452481 / 500000000)) (hi := (640904963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7414835549 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7414835549 / 3906250000) = 1/(3906250000 / 7414835549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (320452481 / 500000000) (640904963 / 1000000000) (Real.log (7414835549 / 3906250000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7414835549 / 3906250000) = -Real.log (3906250000 / 7414835549) := by
    rw [show ((7414835549 / 3906250000) : ℝ) = ((3906250000 / 7414835549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (641849841 / 1000000000) ≤ -Real.log (500000000000 / 949996157511) ∧
    -Real.log (500000000000 / 949996157511) ≤ (320924921 / 500000000) := by
  have h := checkLog_sound (w := (449996157511 / 1449996157511)) (n := 12)
    (lo := (641849841 / 1000000000)) (hi := (320924921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((949996157511 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(949996157511 / 500000000000) = 1/(500000000000 / 949996157511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (641849841 / 1000000000) (320924921 / 500000000) (Real.log (949996157511 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (949996157511 / 500000000000) = -Real.log (500000000000 / 949996157511) := by
    rw [show ((949996157511 / 500000000000) : ℝ) = ((500000000000 / 949996157511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (229053483 / 500000000) ≤ -Real.log (125000000000 / 197634764541) ∧
    -Real.log (125000000000 / 197634764541) ≤ (458106967 / 1000000000) := by
  have h := checkLog_sound (w := (72634764541 / 322634764541)) (n := 12)
    (lo := (229053483 / 500000000)) (hi := (458106967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197634764541 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197634764541 / 125000000000) = 1/(125000000000 / 197634764541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (229053483 / 500000000) (458106967 / 1000000000) (Real.log (197634764541 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (197634764541 / 125000000000) = -Real.log (125000000000 / 197634764541) := by
    rw [show ((197634764541 / 125000000000) : ℝ) = ((125000000000 / 197634764541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (14337373 / 31250000) ≤ -Real.log (50000000000 / 79108390367) ∧
    -Real.log (50000000000 / 79108390367) ≤ (458795937 / 1000000000) := by
  have h := checkLog_sound (w := (29108390367 / 129108390367)) (n := 12)
    (lo := (14337373 / 31250000)) (hi := (458795937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79108390367 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79108390367 / 50000000000) = 1/(50000000000 / 79108390367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (14337373 / 31250000) (458795937 / 1000000000) (Real.log (79108390367 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (79108390367 / 50000000000) = -Real.log (50000000000 / 79108390367) := by
    rw [show ((79108390367 / 50000000000) : ℝ) = ((50000000000 / 79108390367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0414
