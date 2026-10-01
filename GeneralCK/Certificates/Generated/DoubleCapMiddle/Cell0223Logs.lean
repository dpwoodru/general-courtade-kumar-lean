import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0223
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

theorem reflection_log_1_neg : (255277917 / 1000000000) ≤ -Real.log (5120 / 6609) ∧
    -Real.log (5120 / 6609) ≤ (127638959 / 500000000) := by
  have h := checkLog_sound (w := (1489 / 11729)) (n := 12)
    (lo := (255277917 / 1000000000)) (hi := (127638959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6609 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6609 / 5120) = 1/(5120 / 6609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (255277917 / 1000000000) (127638959 / 500000000) (Real.log (6609 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6609 / 5120) = -Real.log (5120 / 6609) := by
    rw [show ((6609 / 5120) : ℝ) = ((5120 / 6609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (171823173 / 500000000) ≤ -Real.log (3631 / 5120) ∧
    -Real.log (3631 / 5120) ≤ (343646347 / 1000000000) := by
  have h := checkLog_sound (w := (1489 / 8751)) (n := 12)
    (lo := (171823173 / 500000000)) (hi := (343646347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3631) = 1/(3631 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-343646347 / 1000000000) (-171823173 / 500000000) (Real.log (3631 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (254823887 / 1000000000) ≤ -Real.log (2560 / 3303) ∧
    -Real.log (2560 / 3303) ≤ (15926493 / 62500000) := by
  have h := checkLog_sound (w := (743 / 5863)) (n := 12)
    (lo := (254823887 / 1000000000)) (hi := (15926493 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3303 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3303 / 2560) = 1/(2560 / 3303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (254823887 / 1000000000) (15926493 / 62500000) (Real.log (3303 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3303 / 2560) = -Real.log (2560 / 3303) := by
    rw [show ((3303 / 2560) : ℝ) = ((2560 / 3303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (342820469 / 1000000000) ≤ -Real.log (1817 / 2560) ∧
    -Real.log (1817 / 2560) ≤ (34282047 / 100000000) := by
  have h := checkLog_sound (w := (743 / 4377)) (n := 12)
    (lo := (342820469 / 1000000000)) (hi := (34282047 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1817) = 1/(1817 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-34282047 / 100000000) (-342820469 / 1000000000) (Real.log (1817 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (229231339 / 500000000) ≤ -Real.log (2560 / 4049) ∧
    -Real.log (2560 / 4049) ≤ (458462679 / 1000000000) := by
  have h := checkLog_sound (w := (1489 / 6609)) (n := 12)
    (lo := (229231339 / 500000000)) (hi := (458462679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4049 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4049 / 2560) = 1/(2560 / 4049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (229231339 / 500000000) (458462679 / 1000000000) (Real.log (4049 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4049 / 2560) = -Real.log (2560 / 4049) := by
    rw [show ((4049 / 2560) : ℝ) = ((2560 / 4049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (435707233 / 500000000) ≤ -Real.log (1071 / 2560) ∧
    -Real.log (1071 / 2560) ≤ (217853617 / 250000000) := by
  have h := checkLog_sound (w := (209 / 2351)) (n := 12)
    (lo := (89133643 / 500000000)) (hi := (178267287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1071) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1071) = 1/(1071 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-217853617 / 250000000) (-435707233 / 500000000) (Real.log (1071 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (11443037 / 25000000) ≤ -Real.log (1280 / 2023) ∧
    -Real.log (1280 / 2023) ≤ (457721481 / 1000000000) := by
  have h := checkLog_sound (w := (743 / 3303)) (n := 12)
    (lo := (11443037 / 25000000)) (hi := (457721481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2023 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2023 / 1280) = 1/(1280 / 2023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (11443037 / 25000000) (457721481 / 1000000000) (Real.log (2023 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2023 / 1280) = -Real.log (1280 / 2023) := by
    rw [show ((2023 / 1280) : ℝ) = ((1280 / 2023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (868617261 / 1000000000) ≤ -Real.log (537 / 1280) ∧
    -Real.log (537 / 1280) ≤ (868617263 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 1177)) (n := 12)
    (lo := (175470081 / 1000000000)) (hi := (87735041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 537) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 537) = 1/(537 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-868617263 / 1000000000) (-868617261 / 1000000000) (Real.log (537 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (174344369 / 500000000) ≤ -Real.log (125000 / 177151) ∧
    -Real.log (125000 / 177151) ≤ (348688739 / 1000000000) := by
  have h := checkLog_sound (w := (52151 / 302151)) (n := 12)
    (lo := (174344369 / 500000000)) (hi := (348688739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177151 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177151 / 125000) = 1/(125000 / 177151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (174344369 / 500000000) (348688739 / 1000000000) (Real.log (177151 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (177151 / 125000) = -Real.log (125000 / 177151) := by
    rw [show ((177151 / 125000) : ℝ) = ((125000 / 177151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (539924931 / 1000000000) ≤ -Real.log (72849 / 125000) ∧
    -Real.log (72849 / 125000) ≤ (134981233 / 250000000) := by
  have h := checkLog_sound (w := (52151 / 197849)) (n := 12)
    (lo := (539924931 / 1000000000)) (hi := (134981233 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 72849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 72849) = 1/(72849 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-134981233 / 250000000) (-539924931 / 1000000000) (Real.log (72849 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (43663333 / 125000000) ≤ -Real.log (250000 / 354521) ∧
    -Real.log (250000 / 354521) ≤ (69861333 / 200000000) := by
  have h := checkLog_sound (w := (104521 / 604521)) (n := 12)
    (lo := (43663333 / 125000000)) (hi := (69861333 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((354521 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(354521 / 250000) = 1/(250000 / 354521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (43663333 / 125000000) (69861333 / 200000000) (Real.log (354521 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (354521 / 250000) = -Real.log (250000 / 354521) := by
    rw [show ((354521 / 250000) : ℝ) = ((250000 / 354521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (541429171 / 1000000000) ≤ -Real.log (145479 / 250000) ∧
    -Real.log (145479 / 250000) ≤ (135357293 / 250000000) := by
  have h := checkLog_sound (w := (104521 / 395479)) (n := 12)
    (lo := (541429171 / 1000000000)) (hi := (135357293 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 145479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 145479) = 1/(145479 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-135357293 / 250000000) (-541429171 / 1000000000) (Real.log (145479 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (269965303 / 1000000000) ≤ -Real.log (1000000 / 1309919) ∧
    -Real.log (1000000 / 1309919) ≤ (33745663 / 125000000) := by
  have h := checkLog_sound (w := (309919 / 2309919)) (n := 12)
    (lo := (269965303 / 1000000000)) (hi := (33745663 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1309919 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1309919 / 1000000) = 1/(1000000 / 1309919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (269965303 / 1000000000) (33745663 / 125000000) (Real.log (1309919 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1309919 / 1000000) = -Real.log (1000000 / 1309919) := by
    rw [show ((1309919 / 1000000) : ℝ) = ((1000000 / 1309919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (46368287 / 125000000) ≤ -Real.log (690081 / 1000000) ∧
    -Real.log (690081 / 1000000) ≤ (370946297 / 1000000000) := by
  have h := checkLog_sound (w := (309919 / 1690081)) (n := 12)
    (lo := (46368287 / 125000000)) (hi := (370946297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 690081) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 690081) = 1/(690081 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-370946297 / 1000000000) (-46368287 / 125000000) (Real.log (690081 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (33813969 / 125000000) ≤ -Real.log (200000 / 262127) ∧
    -Real.log (200000 / 262127) ≤ (270511753 / 1000000000) := by
  have h := checkLog_sound (w := (62127 / 462127)) (n := 12)
    (lo := (33813969 / 125000000)) (hi := (270511753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((262127 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(262127 / 200000) = 1/(200000 / 262127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (33813969 / 125000000) (270511753 / 1000000000) (Real.log (262127 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (262127 / 200000) = -Real.log (200000 / 262127) := by
    rw [show ((262127 / 200000) : ℝ) = ((200000 / 262127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (185992197 / 500000000) ≤ -Real.log (137873 / 200000) ∧
    -Real.log (137873 / 200000) ≤ (74396879 / 200000000) := by
  have h := checkLog_sound (w := (62127 / 337873)) (n := 12)
    (lo := (185992197 / 500000000)) (hi := (74396879 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 137873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 137873) = 1/(137873 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-74396879 / 200000000) (-185992197 / 500000000) (Real.log (137873 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (888613669 / 1000000000) ≤ -Real.log (100000000000 / 243175609823) ∧
    -Real.log (100000000000 / 243175609823) ≤ (888613671 / 1000000000) := by
  have h := checkLog_sound (w := (43175609823 / 443175609823)) (n := 12)
    (lo := (195466489 / 1000000000)) (hi := (19546649 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243175609823 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(243175609823 / 200000000000) = 1/(100000000000 / 243175609823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (888613669 / 1000000000) (888613671 / 1000000000) (Real.log (243175609823 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (243175609823 / 100000000000) = -Real.log (100000000000 / 243175609823) := by
    rw [show ((243175609823 / 100000000000) : ℝ) = ((100000000000 / 243175609823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (178147167 / 200000000) ≤ -Real.log (500000000000 / 1218461083731) ∧
    -Real.log (500000000000 / 1218461083731) ≤ (890735837 / 1000000000) := by
  have h := checkLog_sound (w := (218461083731 / 2218461083731)) (n := 12)
    (lo := (39517731 / 200000000)) (hi := (12349291 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1218461083731 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1218461083731 / 1000000000000) = 1/(500000000000 / 1218461083731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (178147167 / 200000000) (890735837 / 1000000000) (Real.log (1218461083731 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1218461083731 / 500000000000) = -Real.log (500000000000 / 1218461083731) := by
    rw [show ((1218461083731 / 500000000000) : ℝ) = ((500000000000 / 1218461083731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1602279 / 2500000) ≤ -Real.log (500000000000 / 949105249963) ∧
    -Real.log (500000000000 / 949105249963) ≤ (640911601 / 1000000000) := by
  have h := checkLog_sound (w := (449105249963 / 1449105249963)) (n := 12)
    (lo := (1602279 / 2500000)) (hi := (640911601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((949105249963 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(949105249963 / 500000000000) = 1/(500000000000 / 949105249963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1602279 / 2500000) (640911601 / 1000000000) (Real.log (949105249963 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (949105249963 / 500000000000) = -Real.log (500000000000 / 949105249963) := by
    rw [show ((949105249963 / 500000000000) : ℝ) = ((500000000000 / 949105249963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (642496147 / 1000000000) ≤ -Real.log (500000000000 / 950610344303) ∧
    -Real.log (500000000000 / 950610344303) ≤ (160624037 / 250000000) := by
  have h := checkLog_sound (w := (450610344303 / 1450610344303)) (n := 12)
    (lo := (642496147 / 1000000000)) (hi := (160624037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((950610344303 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(950610344303 / 500000000000) = 1/(500000000000 / 950610344303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (642496147 / 1000000000) (160624037 / 250000000) (Real.log (950610344303 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (950610344303 / 500000000000) = -Real.log (500000000000 / 950610344303) := by
    rw [show ((950610344303 / 500000000000) : ℝ) = ((500000000000 / 950610344303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0223
