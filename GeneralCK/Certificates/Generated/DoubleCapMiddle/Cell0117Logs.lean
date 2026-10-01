import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0117
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

theorem reflection_log_1_neg : (319021751 / 1000000000) ≤ -Real.log (1280 / 1761) ∧
    -Real.log (1280 / 1761) ≤ (39877719 / 125000000) := by
  have h := checkLog_sound (w := (481 / 3041)) (n := 12)
    (lo := (319021751 / 1000000000)) (hi := (39877719 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1761 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1761 / 1280) = 1/(1280 / 1761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (319021751 / 1000000000) (39877719 / 125000000) (Real.log (1761 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1761 / 1280) = -Real.log (1280 / 1761) := by
    rw [show ((1761 / 1280) : ℝ) = ((1280 / 1761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (471254411 / 1000000000) ≤ -Real.log (799 / 1280) ∧
    -Real.log (799 / 1280) ≤ (117813603 / 250000000) := by
  have h := checkLog_sound (w := (481 / 2079)) (n := 12)
    (lo := (471254411 / 1000000000)) (hi := (117813603 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 799) = 1/(799 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-117813603 / 250000000) (-471254411 / 1000000000) (Real.log (799 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (318169599 / 1000000000) ≤ -Real.log (2560 / 3519) ∧
    -Real.log (2560 / 3519) ≤ (24857 / 78125) := by
  have h := checkLog_sound (w := (959 / 6079)) (n := 12)
    (lo := (318169599 / 1000000000)) (hi := (24857 / 78125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3519 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3519 / 2560) = 1/(2560 / 3519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (318169599 / 1000000000) (24857 / 78125) (Real.log (3519 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3519 / 2560) = -Real.log (2560 / 3519) := by
    rw [show ((3519 / 2560) : ℝ) = ((2560 / 3519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (58672353 / 125000000) ≤ -Real.log (1601 / 2560) ∧
    -Real.log (1601 / 2560) ≤ (18775153 / 40000000) := by
  have h := checkLog_sound (w := (959 / 4161)) (n := 12)
    (lo := (58672353 / 125000000)) (hi := (18775153 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1601) = 1/(1601 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-18775153 / 40000000) (-58672353 / 125000000) (Real.log (1601 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (280254123 / 500000000) ≤ -Real.log (640 / 1121) ∧
    -Real.log (640 / 1121) ≤ (560508247 / 1000000000) := by
  have h := checkLog_sound (w := (481 / 1761)) (n := 12)
    (lo := (280254123 / 500000000)) (hi := (560508247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1121 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1121 / 640) = 1/(640 / 1121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (280254123 / 500000000) (560508247 / 1000000000) (Real.log (1121 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1121 / 640) = -Real.log (640 / 1121) := by
    rw [show ((1121 / 640) : ℝ) = ((640 / 1121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1392563973 / 1000000000) ≤ -Real.log (159 / 640) ∧
    -Real.log (159 / 640) ≤ (174070497 / 125000000) := by
  have h := checkLog_sound (w := (1 / 319)) (n := 12)
    (lo := (6269613 / 1000000000)) (hi := (3134807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 159) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 159) = 1/(159 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-174070497 / 125000000) (-1392563973 / 1000000000) (Real.log (159 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (559169259 / 1000000000) ≤ -Real.log (1280 / 2239) ∧
    -Real.log (1280 / 2239) ≤ (27958463 / 50000000) := by
  have h := checkLog_sound (w := (959 / 3519)) (n := 12)
    (lo := (559169259 / 1000000000)) (hi := (27958463 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2239 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2239 / 1280) = 1/(1280 / 2239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (559169259 / 1000000000) (27958463 / 50000000) (Real.log (2239 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2239 / 1280) = -Real.log (1280 / 2239) := by
    rw [show ((2239 / 1280) : ℝ) = ((1280 / 2239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1383174233 / 1000000000) ≤ -Real.log (321 / 1280) ∧
    -Real.log (321 / 1280) ≤ (276634847 / 200000000) := by
  have h := checkLog_sound (w := (319 / 961)) (n := 12)
    (lo := (690027053 / 1000000000)) (hi := (345013527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 321) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 321) = 1/(321 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-276634847 / 200000000) (-1383174233 / 1000000000) (Real.log (321 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (435974267 / 1000000000) ≤ -Real.log (1000000 / 1546469) ∧
    -Real.log (1000000 / 1546469) ≤ (108993567 / 250000000) := by
  have h := checkLog_sound (w := (546469 / 2546469)) (n := 12)
    (lo := (435974267 / 1000000000)) (hi := (108993567 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1546469 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1546469 / 1000000) = 1/(1000000 / 1546469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (435974267 / 1000000000) (108993567 / 250000000) (Real.log (1546469 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1546469 / 1000000) = -Real.log (1000000 / 1546469) := by
    rw [show ((1546469 / 1000000) : ℝ) = ((1000000 / 1546469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (790691653 / 1000000000) ≤ -Real.log (453531 / 1000000) ∧
    -Real.log (453531 / 1000000) ≤ (158138331 / 200000000) := by
  have h := checkLog_sound (w := (46469 / 953531)) (n := 12)
    (lo := (97544473 / 1000000000)) (hi := (48772237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 453531) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 453531) = 1/(453531 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-158138331 / 200000000) (-790691653 / 1000000000) (Real.log (453531 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (437174347 / 1000000000) ≤ -Real.log (500000 / 774163) ∧
    -Real.log (500000 / 774163) ≤ (109293587 / 250000000) := by
  have h := checkLog_sound (w := (274163 / 1274163)) (n := 12)
    (lo := (437174347 / 1000000000)) (hi := (109293587 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((774163 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(774163 / 500000) = 1/(500000 / 774163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (437174347 / 1000000000) (109293587 / 250000000) (Real.log (774163 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (774163 / 500000) = -Real.log (500000 / 774163) := by
    rw [show ((774163 / 500000) : ℝ) = ((500000 / 774163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (794794597 / 1000000000) ≤ -Real.log (225837 / 500000) ∧
    -Real.log (225837 / 500000) ≤ (794794599 / 1000000000) := by
  have h := checkLog_sound (w := (24163 / 475837)) (n := 12)
    (lo := (101647417 / 1000000000)) (hi := (50823709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225837) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 225837) = 1/(225837 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-794794599 / 1000000000) (-794794597 / 1000000000) (Real.log (225837 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (175693443 / 500000000) ≤ -Real.log (1000000 / 1421037) ∧
    -Real.log (1000000 / 1421037) ≤ (351386887 / 1000000000) := by
  have h := checkLog_sound (w := (421037 / 2421037)) (n := 12)
    (lo := (175693443 / 500000000)) (hi := (351386887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1421037 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1421037 / 1000000) = 1/(1000000 / 1421037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (175693443 / 500000000) (351386887 / 1000000000) (Real.log (1421037 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1421037 / 1000000) = -Real.log (1000000 / 1421037) := by
    rw [show ((1421037 / 1000000) : ℝ) = ((1000000 / 1421037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (273258353 / 500000000) ≤ -Real.log (578963 / 1000000) ∧
    -Real.log (578963 / 1000000) ≤ (546516707 / 1000000000) := by
  have h := checkLog_sound (w := (421037 / 1578963)) (n := 12)
    (lo := (273258353 / 500000000)) (hi := (546516707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 578963) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 578963) = 1/(578963 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-546516707 / 1000000000) (-273258353 / 500000000) (Real.log (578963 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (352573343 / 1000000000) ≤ -Real.log (250000 / 355681) ∧
    -Real.log (250000 / 355681) ≤ (11017917 / 31250000) := by
  have h := checkLog_sound (w := (105681 / 605681)) (n := 12)
    (lo := (352573343 / 1000000000)) (hi := (11017917 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355681 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355681 / 250000) = 1/(250000 / 355681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (352573343 / 1000000000) (11017917 / 31250000) (Real.log (355681 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (355681 / 250000) = -Real.log (250000 / 355681) := by
    rw [show ((355681 / 250000) : ℝ) = ((250000 / 355681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (54943479 / 100000000) ≤ -Real.log (144319 / 250000) ∧
    -Real.log (144319 / 250000) ≤ (549434791 / 1000000000) := by
  have h := checkLog_sound (w := (105681 / 394319)) (n := 12)
    (lo := (54943479 / 100000000)) (hi := (549434791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 144319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 144319) = 1/(144319 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-549434791 / 1000000000) (-54943479 / 100000000) (Real.log (144319 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1226665921 / 1000000000) ≤ -Real.log (500000000000 / 1704920942559) ∧
    -Real.log (500000000000 / 1704920942559) ≤ (1226665923 / 1000000000) := by
  have h := checkLog_sound (w := (704920942559 / 2704920942559)) (n := 12)
    (lo := (533518741 / 1000000000)) (hi := (266759371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1704920942559 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1704920942559 / 1000000000000) = 1/(500000000000 / 1704920942559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1226665921 / 1000000000) (1226665923 / 1000000000) (Real.log (1704920942559 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1704920942559 / 500000000000) = -Real.log (500000000000 / 1704920942559) := by
    rw [show ((1704920942559 / 500000000000) : ℝ) = ((500000000000 / 1704920942559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (246393789 / 200000000) ≤ -Real.log (500000000000 / 1713986193583) ∧
    -Real.log (500000000000 / 1713986193583) ≤ (1231968947 / 1000000000) := by
  have h := checkLog_sound (w := (713986193583 / 2713986193583)) (n := 12)
    (lo := (107764353 / 200000000)) (hi := (269410883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1713986193583 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1713986193583 / 1000000000000) = 1/(500000000000 / 1713986193583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (246393789 / 200000000) (1231968947 / 1000000000) (Real.log (1713986193583 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1713986193583 / 500000000000) = -Real.log (500000000000 / 1713986193583) := by
    rw [show ((1713986193583 / 500000000000) : ℝ) = ((500000000000 / 1713986193583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (112237949 / 125000000) ≤ -Real.log (62500000000 / 153403261521) ∧
    -Real.log (62500000000 / 153403261521) ≤ (448951797 / 500000000) := by
  have h := checkLog_sound (w := (28403261521 / 278403261521)) (n := 12)
    (lo := (51189103 / 250000000)) (hi := (204756413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153403261521 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(153403261521 / 125000000000) = 1/(62500000000 / 153403261521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (112237949 / 125000000) (448951797 / 500000000) (Real.log (153403261521 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (153403261521 / 62500000000) = -Real.log (62500000000 / 153403261521) := by
    rw [show ((153403261521 / 62500000000) : ℝ) = ((62500000000 / 153403261521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (902008133 / 1000000000) ≤ -Real.log (500000000000 / 1232273643803) ∧
    -Real.log (500000000000 / 1232273643803) ≤ (180401627 / 200000000) := by
  have h := checkLog_sound (w := (232273643803 / 2232273643803)) (n := 12)
    (lo := (208860953 / 1000000000)) (hi := (104430477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1232273643803 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1232273643803 / 1000000000000) = 1/(500000000000 / 1232273643803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (902008133 / 1000000000) (180401627 / 200000000) (Real.log (1232273643803 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1232273643803 / 500000000000) = -Real.log (500000000000 / 1232273643803) := by
    rw [show ((1232273643803 / 500000000000) : ℝ) = ((500000000000 / 1232273643803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0117
