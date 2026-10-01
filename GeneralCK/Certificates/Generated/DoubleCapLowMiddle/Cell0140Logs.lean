import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0140
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

theorem reflection_log_1_neg : (164607593 / 250000000) ≤ -Real.log (25600 / 49453) ∧
    -Real.log (25600 / 49453) ≤ (658430373 / 1000000000) := by
  have h := checkLog_sound (w := (23853 / 75053)) (n := 12)
    (lo := (164607593 / 250000000)) (hi := (658430373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49453 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49453 / 25600) = 1/(25600 / 49453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (164607593 / 250000000) (658430373 / 1000000000) (Real.log (49453 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (49453 / 25600) = -Real.log (25600 / 49453) := by
    rw [show ((49453 / 25600) : ℝ) = ((25600 / 49453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1342346159 / 500000000) ≤ -Real.log (1747 / 25600) ∧
    -Real.log (1747 / 25600) ≤ (1342346161 / 500000000) := by
  have h := checkLog_sound (w := (1453 / 4947)) (n := 12)
    (lo := (302625389 / 500000000)) (hi := (605250779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1747) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1747) = 1/(1747 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1342346161 / 500000000) (-1342346159 / 500000000) (Real.log (1747 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (131609219 / 200000000) ≤ -Real.log (12800 / 24717) ∧
    -Real.log (12800 / 24717) ≤ (41127881 / 62500000) := by
  have h := checkLog_sound (w := (11917 / 37517)) (n := 12)
    (lo := (131609219 / 200000000)) (hi := (41127881 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24717 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24717 / 12800) = 1/(12800 / 24717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (131609219 / 200000000) (41127881 / 62500000) (Real.log (24717 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24717 / 12800) = -Real.log (12800 / 24717) := by
    rw [show ((24717 / 12800) : ℝ) = ((12800 / 24717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2673875247 / 1000000000) ≤ -Real.log (883 / 12800) ∧
    -Real.log (883 / 12800) ≤ (2673875251 / 1000000000) := by
  have h := checkLog_sound (w := (717 / 2483)) (n := 12)
    (lo := (594433707 / 1000000000)) (hi := (148608427 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 883) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 883) = 1/(883 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2673875251 / 1000000000) (-2673875247 / 1000000000) (Real.log (883 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (77808103 / 125000000) ≤ -Real.log (12800 / 23853) ∧
    -Real.log (12800 / 23853) ≤ (24898593 / 40000000) := by
  have h := checkLog_sound (w := (11053 / 36653)) (n := 12)
    (lo := (77808103 / 125000000)) (hi := (24898593 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23853 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23853 / 12800) = 1/(12800 / 23853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (77808103 / 125000000) (24898593 / 40000000) (Real.log (23853 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (23853 / 12800) = -Real.log (12800 / 23853) := by
    rw [show ((23853 / 12800) : ℝ) = ((12800 / 23853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (995772569 / 500000000) ≤ -Real.log (1747 / 12800) ∧
    -Real.log (1747 / 12800) ≤ (1991545141 / 1000000000) := by
  have h := checkLog_sound (w := (1453 / 4947)) (n := 12)
    (lo := (302625389 / 500000000)) (hi := (605250779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1747) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3200 / 1747) = 1/(1747 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1991545141 / 1000000000) (-995772569 / 500000000) (Real.log (1747 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (621667961 / 1000000000) ≤ -Real.log (6400 / 11917) ∧
    -Real.log (6400 / 11917) ≤ (310833981 / 500000000) := by
  have h := checkLog_sound (w := (5517 / 18317)) (n := 12)
    (lo := (621667961 / 1000000000)) (hi := (310833981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11917 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11917 / 6400) = 1/(6400 / 11917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (621667961 / 1000000000) (310833981 / 500000000) (Real.log (11917 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11917 / 6400) = -Real.log (6400 / 11917) := by
    rw [show ((11917 / 6400) : ℝ) = ((6400 / 11917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1980728067 / 1000000000) ≤ -Real.log (883 / 6400) ∧
    -Real.log (883 / 6400) ≤ (198072807 / 100000000) := by
  have h := checkLog_sound (w := (717 / 2483)) (n := 12)
    (lo := (594433707 / 1000000000)) (hi := (148608427 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 883) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 883) = 1/(883 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-198072807 / 100000000) (-1980728067 / 1000000000) (Real.log (883 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (665388447 / 1000000000) ≤ -Real.log (500000 / 972623) ∧
    -Real.log (500000 / 972623) ≤ (20793389 / 31250000) := by
  have h := checkLog_sound (w := (472623 / 1472623)) (n := 12)
    (lo := (665388447 / 1000000000)) (hi := (20793389 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((972623 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(972623 / 500000) = 1/(500000 / 972623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (665388447 / 1000000000) (20793389 / 31250000) (Real.log (972623 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (972623 / 500000) = -Real.log (500000 / 972623) := by
    rw [show ((972623 / 500000) : ℝ) = ((500000 / 972623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2904904851 / 1000000000) ≤ -Real.log (27377 / 500000) ∧
    -Real.log (27377 / 500000) ≤ (363113107 / 125000000) := by
  have h := checkLog_sound (w := (3873 / 58627)) (n := 12)
    (lo := (132316131 / 1000000000)) (hi := (33079033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27377) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 27377) = 1/(27377 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-363113107 / 125000000) (-2904904851 / 1000000000) (Real.log (27377 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (166416759 / 250000000) ≤ -Real.log (250000 / 486447) ∧
    -Real.log (250000 / 486447) ≤ (665667037 / 1000000000) := by
  have h := checkLog_sound (w := (236447 / 736447)) (n := 12)
    (lo := (166416759 / 250000000)) (hi := (665667037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((486447 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(486447 / 250000) = 1/(250000 / 486447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (166416759 / 250000000) (665667037 / 1000000000) (Real.log (486447 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (486447 / 250000) = -Real.log (250000 / 486447) := by
    rw [show ((486447 / 250000) : ℝ) = ((250000 / 486447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (291485299 / 100000000) ≤ -Real.log (13553 / 250000) ∧
    -Real.log (13553 / 250000) ≤ (582970599 / 200000000) := by
  have h := checkLog_sound (w := (1036 / 14589)) (n := 12)
    (lo := (14226427 / 100000000)) (hi := (142264271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13553) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 13553) = 1/(13553 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-582970599 / 200000000) (-291485299 / 100000000) (Real.log (13553 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (166218303 / 250000000) ≤ -Real.log (250000 / 486061) ∧
    -Real.log (250000 / 486061) ≤ (664873213 / 1000000000) := by
  have h := checkLog_sound (w := (236061 / 736061)) (n := 12)
    (lo := (166218303 / 250000000)) (hi := (664873213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((486061 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(486061 / 250000) = 1/(250000 / 486061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (166218303 / 250000000) (664873213 / 1000000000) (Real.log (486061 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (486061 / 250000) = -Real.log (250000 / 486061) := by
    rw [show ((486061 / 250000) : ℝ) = ((250000 / 486061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (360846281 / 125000000) ≤ -Real.log (13939 / 250000) ∧
    -Real.log (13939 / 250000) ≤ (2886770253 / 1000000000) := by
  have h := checkLog_sound (w := (843 / 14782)) (n := 12)
    (lo := (14272691 / 125000000)) (hi := (114181529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13939) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 13939) = 1/(13939 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2886770253 / 1000000000) (-360846281 / 125000000) (Real.log (13939 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (51966 / 78125) ≤ -Real.log (1000000 / 1944811) ∧
    -Real.log (1000000 / 1944811) ≤ (665164801 / 1000000000) := by
  have h := checkLog_sound (w := (944811 / 2944811)) (n := 12)
    (lo := (51966 / 78125)) (hi := (665164801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1944811 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1944811 / 1000000) = 1/(1000000 / 1944811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (51966 / 78125) (665164801 / 1000000000) (Real.log (1944811 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1944811 / 1000000) = -Real.log (1000000 / 1944811) := by
    rw [show ((1944811 / 1000000) : ℝ) = ((1000000 / 1944811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1448495809 / 500000000) ≤ -Real.log (55189 / 1000000) ∧
    -Real.log (55189 / 1000000) ≤ (2896991623 / 1000000000) := by
  have h := checkLog_sound (w := (7311 / 117689)) (n := 12)
    (lo := (62201449 / 500000000)) (hi := (124402899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 55189) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 55189) = 1/(55189 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2896991623 / 1000000000) (-1448495809 / 500000000) (Real.log (55189 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1785146649 / 500000000) ≤ -Real.log (100000000000 / 3552701172517) ∧
    -Real.log (100000000000 / 3552701172517) ≤ (446286663 / 125000000) := by
  have h := checkLog_sound (w := (352701172517 / 6752701172517)) (n := 12)
    (lo := (52278699 / 500000000)) (hi := (104557399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3552701172517 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3552701172517 / 3200000000000) = 1/(100000000000 / 3552701172517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1785146649 / 500000000) (446286663 / 125000000) (Real.log (3552701172517 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (3552701172517 / 100000000000) = -Real.log (100000000000 / 3552701172517) := by
    rw [show ((3552701172517 / 100000000000) : ℝ) = ((100000000000 / 3552701172517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1790260013 / 500000000) ≤ -Real.log (125000000000 / 4486525123589) ∧
    -Real.log (125000000000 / 4486525123589) ≤ (111891251 / 31250000) := by
  have h := checkLog_sound (w := (486525123589 / 8486525123589)) (n := 12)
    (lo := (57392063 / 500000000)) (hi := (114784127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4486525123589 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4486525123589 / 4000000000000) = 1/(125000000000 / 4486525123589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1790260013 / 500000000) (111891251 / 31250000) (Real.log (4486525123589 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (4486525123589 / 125000000000) = -Real.log (125000000000 / 4486525123589) := by
    rw [show ((4486525123589 / 125000000000) : ℝ) = ((125000000000 / 4486525123589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (177582173 / 50000000) ≤ -Real.log (125000000000 / 4358822368893) ∧
    -Real.log (125000000000 / 4358822368893) ≤ (1775821733 / 500000000) := by
  have h := checkLog_sound (w := (358822368893 / 8358822368893)) (n := 12)
    (lo := (2147689 / 25000000)) (hi := (85907561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4358822368893 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(4358822368893 / 4000000000000) = 1/(125000000000 / 4358822368893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (177582173 / 50000000) (1775821733 / 500000000) (Real.log (4358822368893 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4358822368893 / 125000000000) = -Real.log (125000000000 / 4358822368893) := by
    rw [show ((4358822368893 / 125000000000) : ℝ) = ((125000000000 / 4358822368893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1781078209 / 500000000) ≤ -Real.log (500000000000 / 17619552809437) ∧
    -Real.log (500000000000 / 17619552809437) ≤ (445269553 / 125000000) := by
  have h := checkLog_sound (w := (1619552809437 / 33619552809437)) (n := 12)
    (lo := (48210259 / 500000000)) (hi := (96420519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17619552809437 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(17619552809437 / 16000000000000) = 1/(500000000000 / 17619552809437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1781078209 / 500000000) (445269553 / 125000000) (Real.log (17619552809437 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (17619552809437 / 500000000000) = -Real.log (500000000000 / 17619552809437) := by
    rw [show ((17619552809437 / 500000000000) : ℝ) = ((500000000000 / 17619552809437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0140
