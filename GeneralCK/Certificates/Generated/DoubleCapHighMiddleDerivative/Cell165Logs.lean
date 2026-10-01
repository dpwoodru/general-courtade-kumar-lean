import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell165
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

theorem reflection_log_1_neg : (11923083 / 40000000) ≤ -Real.log (2560 / 3449) ∧
    -Real.log (2560 / 3449) ≤ (74519269 / 250000000) := by
  have h := checkLog_sound (w := (889 / 6009)) (n := 12)
    (lo := (11923083 / 40000000)) (hi := (74519269 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3449 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3449 / 2560) = 1/(2560 / 3449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11923083 / 40000000) (74519269 / 250000000) (Real.log (3449 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3449 / 2560) = -Real.log (2560 / 3449) := by
    rw [show ((3449 / 2560) : ℝ) = ((2560 / 3449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (26661563 / 62500000) ≤ -Real.log (1671 / 2560) ∧
    -Real.log (1671 / 2560) ≤ (426585009 / 1000000000) := by
  have h := checkLog_sound (w := (889 / 4231)) (n := 12)
    (lo := (26661563 / 62500000)) (hi := (426585009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1671) = 1/(1671 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-426585009 / 1000000000) (-26661563 / 62500000) (Real.log (1671 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (37205259 / 125000000) ≤ -Real.log (1024 / 1379) ∧
    -Real.log (1024 / 1379) ≤ (297642073 / 1000000000) := by
  have h := checkLog_sound (w := (355 / 2403)) (n := 12)
    (lo := (37205259 / 125000000)) (hi := (297642073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1379 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1379 / 1024) = 1/(1024 / 1379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (37205259 / 125000000) (297642073 / 1000000000) (Real.log (1379 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1379 / 1024) = -Real.log (1024 / 1379) := by
    rw [show ((1379 / 1024) : ℝ) = ((1024 / 1379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (85137549 / 200000000) ≤ -Real.log (669 / 1024) ∧
    -Real.log (669 / 1024) ≤ (212843873 / 500000000) := by
  have h := checkLog_sound (w := (355 / 1693)) (n := 12)
    (lo := (85137549 / 200000000)) (hi := (212843873 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 669) = 1/(669 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-212843873 / 500000000) (-85137549 / 200000000) (Real.log (669 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (220285069 / 1000000000) ≤ -Real.log (31250 / 38951) ∧
    -Real.log (31250 / 38951) ≤ (22028507 / 100000000) := by
  have h := checkLog_sound (w := (7701 / 70201)) (n := 12)
    (lo := (220285069 / 1000000000)) (hi := (22028507 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38951 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38951 / 31250) = 1/(31250 / 38951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (220285069 / 1000000000) (22028507 / 100000000) (Real.log (38951 / 31250)) := by
  have h := reflection_log_5_neg
  have he : Real.log (38951 / 31250) = -Real.log (31250 / 38951) := by
    rw [show ((38951 / 31250) : ℝ) = ((31250 / 38951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (282936019 / 1000000000) ≤ -Real.log (23549 / 31250) ∧
    -Real.log (23549 / 31250) ≤ (14146801 / 50000000) := by
  have h := checkLog_sound (w := (7701 / 54799)) (n := 12)
    (lo := (282936019 / 1000000000)) (hi := (14146801 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 23549) = 1/(23549 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-14146801 / 50000000) (-282936019 / 1000000000) (Real.log (23549 / 31250)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (110311789 / 500000000) ≤ -Real.log (500000 / 623427) ∧
    -Real.log (500000 / 623427) ≤ (220623579 / 1000000000) := by
  have h := checkLog_sound (w := (123427 / 1123427)) (n := 12)
    (lo := (110311789 / 500000000)) (hi := (220623579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((623427 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(623427 / 500000) = 1/(500000 / 623427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (110311789 / 500000000) (220623579 / 1000000000) (Real.log (623427 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (623427 / 500000) = -Real.log (500000 / 623427) := by
    rw [show ((623427 / 500000) : ℝ) = ((500000 / 623427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (141748089 / 500000000) ≤ -Real.log (376573 / 500000) ∧
    -Real.log (376573 / 500000) ≤ (283496179 / 1000000000) := by
  have h := checkLog_sound (w := (123427 / 876573)) (n := 12)
    (lo := (141748089 / 500000000)) (hi := (283496179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 376573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 376573) = 1/(376573 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-283496179 / 1000000000) (-141748089 / 500000000) (Real.log (376573 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (40792117 / 250000000) ≤ -Real.log (200000 / 235447) ∧
    -Real.log (200000 / 235447) ≤ (163168469 / 1000000000) := by
  have h := checkLog_sound (w := (35447 / 435447)) (n := 12)
    (lo := (40792117 / 250000000)) (hi := (163168469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((235447 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(235447 / 200000) = 1/(200000 / 235447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (40792117 / 250000000) (163168469 / 1000000000) (Real.log (235447 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (235447 / 200000) = -Real.log (200000 / 235447) := by
    rw [show ((235447 / 200000) : ℝ) = ((200000 / 235447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (195084659 / 1000000000) ≤ -Real.log (164553 / 200000) ∧
    -Real.log (164553 / 200000) ≤ (9754233 / 50000000) := by
  have h := checkLog_sound (w := (35447 / 364553)) (n := 12)
    (lo := (195084659 / 1000000000)) (hi := (9754233 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 164553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 164553) = 1/(164553 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-9754233 / 50000000) (-195084659 / 1000000000) (Real.log (164553 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (20429501 / 125000000) ≤ -Real.log (20000 / 23551) ∧
    -Real.log (20000 / 23551) ≤ (163436009 / 1000000000) := by
  have h := checkLog_sound (w := (3551 / 43551)) (n := 12)
    (lo := (20429501 / 125000000)) (hi := (163436009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23551 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23551 / 20000) = 1/(20000 / 23551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (20429501 / 125000000) (163436009 / 1000000000) (Real.log (23551 / 20000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (23551 / 20000) = -Real.log (20000 / 23551) := by
    rw [show ((23551 / 20000) : ℝ) = ((20000 / 23551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (48866897 / 250000000) ≤ -Real.log (16449 / 20000) ∧
    -Real.log (16449 / 20000) ≤ (195467589 / 1000000000) := by
  have h := checkLog_sound (w := (3551 / 36449)) (n := 12)
    (lo := (48866897 / 250000000)) (hi := (195467589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 16449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 16449) = 1/(16449 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-195467589 / 1000000000) (-48866897 / 250000000) (Real.log (16449 / 20000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (723329817 / 1000000000) ≤ -Real.log (500000000000 / 1030642750373) ∧
    -Real.log (500000000000 / 1030642750373) ≤ (723329819 / 1000000000) := by
  have h := checkLog_sound (w := (30642750373 / 2030642750373)) (n := 12)
    (lo := (30182637 / 1000000000)) (hi := (15091319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1030642750373 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1030642750373 / 1000000000000) = 1/(500000000000 / 1030642750373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (723329817 / 1000000000) (723329819 / 1000000000) (Real.log (1030642750373 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1030642750373 / 500000000000) = -Real.log (500000000000 / 1030642750373) := by
    rw [show ((1030642750373 / 500000000000) : ℝ) = ((500000000000 / 1030642750373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (724662083 / 1000000000) ≤ -Real.log (250000000000 / 516008378217) ∧
    -Real.log (250000000000 / 516008378217) ≤ (144932417 / 200000000) := by
  have h := checkLog_sound (w := (16008378217 / 1016008378217)) (n := 12)
    (lo := (31514903 / 1000000000)) (hi := (3939363 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((516008378217 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(516008378217 / 500000000000) = 1/(250000000000 / 516008378217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (724662083 / 1000000000) (144932417 / 200000000) (Real.log (516008378217 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (516008378217 / 250000000000) = -Real.log (250000000000 / 516008378217) := by
    rw [show ((516008378217 / 250000000000) : ℝ) = ((250000000000 / 516008378217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (503221089 / 1000000000) ≤ -Real.log (500000000000 / 827020255637) ∧
    -Real.log (500000000000 / 827020255637) ≤ (50322109 / 100000000) := by
  have h := checkLog_sound (w := (327020255637 / 1327020255637)) (n := 12)
    (lo := (503221089 / 1000000000)) (hi := (50322109 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((827020255637 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(827020255637 / 500000000000) = 1/(500000000000 / 827020255637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (503221089 / 1000000000) (50322109 / 100000000) (Real.log (827020255637 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (827020255637 / 500000000000) = -Real.log (500000000000 / 827020255637) := by
    rw [show ((827020255637 / 500000000000) : ℝ) = ((500000000000 / 827020255637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (504119757 / 1000000000) ≤ -Real.log (15625000000 / 25867618961) ∧
    -Real.log (15625000000 / 25867618961) ≤ (252059879 / 500000000) := by
  have h := checkLog_sound (w := (10242618961 / 41492618961)) (n := 12)
    (lo := (504119757 / 1000000000)) (hi := (252059879 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25867618961 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25867618961 / 15625000000) = 1/(15625000000 / 25867618961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (504119757 / 1000000000) (252059879 / 500000000) (Real.log (25867618961 / 15625000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (25867618961 / 15625000000) = -Real.log (15625000000 / 25867618961) := by
    rw [show ((25867618961 / 15625000000) : ℝ) = ((15625000000 / 25867618961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (44781641 / 125000000) ≤ -Real.log (500000000000 / 715413878811) ∧
    -Real.log (500000000000 / 715413878811) ≤ (358253129 / 1000000000) := by
  have h := checkLog_sound (w := (215413878811 / 1215413878811)) (n := 12)
    (lo := (44781641 / 125000000)) (hi := (358253129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((715413878811 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(715413878811 / 500000000000) = 1/(500000000000 / 715413878811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (44781641 / 125000000) (358253129 / 1000000000) (Real.log (715413878811 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (715413878811 / 500000000000) = -Real.log (500000000000 / 715413878811) := by
    rw [show ((715413878811 / 500000000000) : ℝ) = ((500000000000 / 715413878811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (358903597 / 1000000000) ≤ -Real.log (250000000000 / 357939692383) ∧
    -Real.log (250000000000 / 357939692383) ≤ (179451799 / 500000000) := by
  have h := checkLog_sound (w := (107939692383 / 607939692383)) (n := 12)
    (lo := (358903597 / 1000000000)) (hi := (179451799 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357939692383 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357939692383 / 250000000000) = 1/(250000000000 / 357939692383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (358903597 / 1000000000) (179451799 / 500000000) (Real.log (357939692383 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (357939692383 / 250000000000) = -Real.log (250000000000 / 357939692383) := by
    rw [show ((357939692383 / 250000000000) : ℝ) = ((250000000000 / 357939692383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (32031579 / 1000000000) ≤ -Real.log (387390399 / 400000000) ∧
    -Real.log (387390399 / 400000000) ≤ (1601579 / 50000000) := by
  have h := checkLog_sound (w := (12609601 / 787390399)) (n := 12)
    (lo := (32031579 / 1000000000)) (hi := (1601579 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 387390399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 387390399) = 1/(387390399 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-1601579 / 50000000) (-32031579 / 1000000000) (Real.log (387390399 / 400000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (31916191 / 1000000000) ≤ -Real.log (38743510191 / 40000000000) ∧
    -Real.log (38743510191 / 40000000000) ≤ (997381 / 31250000) := by
  have h := checkLog_sound (w := (1256489809 / 78743510191)) (n := 12)
    (lo := (31916191 / 1000000000)) (hi := (997381 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38743510191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38743510191) = 1/(38743510191 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-997381 / 31250000) (-31916191 / 1000000000) (Real.log (38743510191 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell165
