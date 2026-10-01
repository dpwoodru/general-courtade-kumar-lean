import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0124
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

theorem reflection_log_1_neg : (132911761 / 200000000) ≤ -Real.log (25600 / 49757) ∧
    -Real.log (25600 / 49757) ≤ (332279403 / 500000000) := by
  have h := checkLog_sound (w := (24157 / 75357)) (n := 12)
    (lo := (132911761 / 200000000)) (hi := (332279403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49757 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49757 / 25600) = 1/(25600 / 49757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (132911761 / 200000000) (332279403 / 500000000) (Real.log (49757 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49757 / 25600) = -Real.log (25600 / 49757) := by
    rw [show ((49757 / 25600) : ℝ) = ((25600 / 49757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2875868069 / 1000000000) ≤ -Real.log (1443 / 25600) ∧
    -Real.log (1443 / 25600) ≤ (1437934037 / 500000000) := by
  have h := checkLog_sound (w := (157 / 3043)) (n := 12)
    (lo := (103279349 / 1000000000)) (hi := (2065587 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1443) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1443) = 1/(1443 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1437934037 / 500000000) (-2875868069 / 1000000000) (Real.log (1443 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (166044219 / 250000000) ≤ -Real.log (12800 / 24869) ∧
    -Real.log (12800 / 24869) ≤ (664176877 / 1000000000) := by
  have h := checkLog_sound (w := (12069 / 37669)) (n := 12)
    (lo := (166044219 / 250000000)) (hi := (664176877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24869 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24869 / 12800) = 1/(12800 / 24869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (166044219 / 250000000) (664176877 / 1000000000) (Real.log (24869 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24869 / 12800) = -Real.log (12800 / 24869) := by
    rw [show ((24869 / 12800) : ℝ) = ((12800 / 24869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2862786987 / 1000000000) ≤ -Real.log (731 / 12800) ∧
    -Real.log (731 / 12800) ≤ (178924187 / 62500000) := by
  have h := checkLog_sound (w := (69 / 1531)) (n := 12)
    (lo := (90198267 / 1000000000)) (hi := (22549567 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 731) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 731) = 1/(731 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-178924187 / 62500000) (-2862786987 / 1000000000) (Real.log (731 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (317564511 / 500000000) ≤ -Real.log (12800 / 24157) ∧
    -Real.log (12800 / 24157) ≤ (635129023 / 1000000000) := by
  have h := checkLog_sound (w := (11357 / 36957)) (n := 12)
    (lo := (317564511 / 500000000)) (hi := (635129023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24157 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24157 / 12800) = 1/(12800 / 24157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (317564511 / 500000000) (635129023 / 1000000000) (Real.log (24157 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24157 / 12800) = -Real.log (12800 / 24157) := by
    rw [show ((24157 / 12800) : ℝ) = ((12800 / 24157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2182720889 / 1000000000) ≤ -Real.log (1443 / 12800) ∧
    -Real.log (1443 / 12800) ≤ (2182720893 / 1000000000) := by
  have h := checkLog_sound (w := (157 / 3043)) (n := 12)
    (lo := (103279349 / 1000000000)) (hi := (2065587 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1443) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1443) = 1/(1443 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2182720893 / 1000000000) (-2182720889 / 1000000000) (Real.log (1443 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (634342191 / 1000000000) ≤ -Real.log (6400 / 12069) ∧
    -Real.log (6400 / 12069) ≤ (39646387 / 62500000) := by
  have h := checkLog_sound (w := (5669 / 18469)) (n := 12)
    (lo := (634342191 / 1000000000)) (hi := (39646387 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12069 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12069 / 6400) = 1/(6400 / 12069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (634342191 / 1000000000) (39646387 / 62500000) (Real.log (12069 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (12069 / 6400) = -Real.log (6400 / 12069) := by
    rw [show ((12069 / 6400) : ℝ) = ((6400 / 12069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2169639807 / 1000000000) ≤ -Real.log (731 / 6400) ∧
    -Real.log (731 / 6400) ≤ (2169639811 / 1000000000) := by
  have h := checkLog_sound (w := (69 / 1531)) (n := 12)
    (lo := (90198267 / 1000000000)) (hi := (22549567 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 731) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 731) = 1/(731 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2169639811 / 1000000000) (-2169639807 / 1000000000) (Real.log (731 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (334942603 / 500000000) ≤ -Real.log (1000000 / 1954013) ∧
    -Real.log (1000000 / 1954013) ≤ (669885207 / 1000000000) := by
  have h := checkLog_sound (w := (954013 / 2954013)) (n := 12)
    (lo := (334942603 / 500000000)) (hi := (669885207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1954013 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1954013 / 1000000) = 1/(1000000 / 1954013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (334942603 / 500000000) (669885207 / 1000000000) (Real.log (1954013 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1954013 / 1000000) = -Real.log (1000000 / 1954013) := by
    rw [show ((1954013 / 1000000) : ℝ) = ((1000000 / 1954013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (192462283 / 62500000) ≤ -Real.log (45987 / 1000000) ∧
    -Real.log (45987 / 1000000) ≤ (3079396533 / 1000000000) := by
  have h := checkLog_sound (w := (16513 / 108487)) (n := 12)
    (lo := (599234 / 1953125)) (hi := (306807809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 45987) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 45987) = 1/(45987 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3079396533 / 1000000000) (-192462283 / 62500000) (Real.log (45987 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (33508511 / 50000000) ≤ -Real.log (100000 / 195457) ∧
    -Real.log (100000 / 195457) ≤ (670170221 / 1000000000) := by
  have h := checkLog_sound (w := (95457 / 295457)) (n := 12)
    (lo := (33508511 / 50000000)) (hi := (670170221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((195457 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(195457 / 100000) = 1/(100000 / 195457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (33508511 / 50000000) (670170221 / 1000000000) (Real.log (195457 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (195457 / 100000) = -Real.log (100000 / 195457) := by
    rw [show ((195457 / 100000) : ℝ) = ((100000 / 195457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (772895649 / 250000000) ≤ -Real.log (4543 / 100000) ∧
    -Real.log (4543 / 100000) ≤ (3091582601 / 1000000000) := by
  have h := checkLog_sound (w := (1707 / 10793)) (n := 12)
    (lo := (79748469 / 250000000)) (hi := (318993877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4543) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250 / 4543) = 1/(4543 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3091582601 / 1000000000) (-772895649 / 250000000) (Real.log (4543 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (334776507 / 500000000) ≤ -Real.log (250000 / 488341) ∧
    -Real.log (250000 / 488341) ≤ (133910603 / 200000000) := by
  have h := checkLog_sound (w := (238341 / 738341)) (n := 12)
    (lo := (334776507 / 500000000)) (hi := (133910603 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((488341 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(488341 / 250000) = 1/(250000 / 488341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (334776507 / 500000000) (133910603 / 200000000) (Real.log (488341 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (488341 / 250000) = -Real.log (250000 / 488341) := by
    rw [show ((488341 / 250000) : ℝ) = ((250000 / 488341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3065382501 / 1000000000) ≤ -Real.log (11659 / 250000) ∧
    -Real.log (11659 / 250000) ≤ (1532691253 / 500000000) := by
  have h := checkLog_sound (w := (1983 / 13642)) (n := 12)
    (lo := (292793781 / 1000000000)) (hi := (146396891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11659) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 11659) = 1/(11659 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1532691253 / 500000000) (-3065382501 / 1000000000) (Real.log (11659 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (133969467 / 200000000) ≤ -Real.log (1000000 / 1953939) ∧
    -Real.log (1000000 / 1953939) ≤ (83730917 / 125000000) := by
  have h := checkLog_sound (w := (953939 / 2953939)) (n := 12)
    (lo := (133969467 / 200000000)) (hi := (83730917 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1953939 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1953939 / 1000000) = 1/(1000000 / 1953939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (133969467 / 200000000) (83730917 / 125000000) (Real.log (1953939 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1953939 / 1000000) = -Real.log (1000000 / 1953939) := by
    rw [show ((1953939 / 1000000) : ℝ) = ((1000000 / 1953939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3077788671 / 1000000000) ≤ -Real.log (46061 / 1000000) ∧
    -Real.log (46061 / 1000000) ≤ (769447169 / 250000000) := by
  have h := checkLog_sound (w := (16439 / 108561)) (n := 12)
    (lo := (305199951 / 1000000000)) (hi := (19074997 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46061) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 46061) = 1/(46061 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-769447169 / 250000000) (-3077788671 / 1000000000) (Real.log (46061 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1874640867 / 500000000) ≤ -Real.log (62500000000 / 2655659479853) ∧
    -Real.log (62500000000 / 2655659479853) ≤ (187464087 / 50000000) := by
  have h := checkLog_sound (w := (655659479853 / 4655659479853)) (n := 12)
    (lo := (141772917 / 500000000)) (hi := (56709167 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2655659479853 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2655659479853 / 2000000000000) = 1/(62500000000 / 2655659479853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1874640867 / 500000000) (187464087 / 50000000) (Real.log (2655659479853 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2655659479853 / 62500000000) = -Real.log (62500000000 / 2655659479853) := by
    rw [show ((2655659479853 / 62500000000) : ℝ) = ((62500000000 / 2655659479853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (235109551 / 62500000) ≤ -Real.log (500000000000 / 21511886418667) ∧
    -Real.log (500000000000 / 21511886418667) ≤ (1880876411 / 500000000) := by
  have h := checkLog_sound (w := (5511886418667 / 37511886418667)) (n := 12)
    (lo := (74004229 / 250000000)) (hi := (296016917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21511886418667 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(21511886418667 / 16000000000000) = 1/(500000000000 / 21511886418667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (235109551 / 62500000) (1880876411 / 500000000) (Real.log (21511886418667 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (21511886418667 / 500000000000) = -Real.log (500000000000 / 21511886418667) := by
    rw [show ((21511886418667 / 500000000000) : ℝ) = ((500000000000 / 21511886418667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (746987103 / 200000000) ≤ -Real.log (500000000000 / 20942662320953) ∧
    -Real.log (500000000000 / 20942662320953) ≤ (3734935521 / 1000000000) := by
  have h := checkLog_sound (w := (4942662320953 / 36942662320953)) (n := 12)
    (lo := (53839923 / 200000000)) (hi := (1051561 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20942662320953 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(20942662320953 / 16000000000000) = 1/(500000000000 / 20942662320953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (746987103 / 200000000) (3734935521 / 1000000000) (Real.log (20942662320953 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (20942662320953 / 500000000000) = -Real.log (500000000000 / 20942662320953) := by
    rw [show ((20942662320953 / 500000000000) : ℝ) = ((500000000000 / 20942662320953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1873818003 / 500000000) ≤ -Real.log (100000000000 / 4242068127049) ∧
    -Real.log (100000000000 / 4242068127049) ≤ (936909003 / 250000000) := by
  have h := checkLog_sound (w := (1042068127049 / 7442068127049)) (n := 12)
    (lo := (140950053 / 500000000)) (hi := (281900107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4242068127049 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4242068127049 / 3200000000000) = 1/(100000000000 / 4242068127049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1873818003 / 500000000) (936909003 / 250000000) (Real.log (4242068127049 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4242068127049 / 100000000000) = -Real.log (100000000000 / 4242068127049) := by
    rw [show ((4242068127049 / 100000000000) : ℝ) = ((100000000000 / 4242068127049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0124
