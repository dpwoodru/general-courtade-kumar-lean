import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0147
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

theorem reflection_log_1_neg : (327868663 / 500000000) ≤ -Real.log (640 / 1233) ∧
    -Real.log (640 / 1233) ≤ (655737327 / 1000000000) := by
  have h := checkLog_sound (w := (593 / 1873)) (n := 12)
    (lo := (327868663 / 500000000)) (hi := (655737327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1233 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1233 / 640) = 1/(640 / 1233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (327868663 / 500000000) (655737327 / 1000000000) (Real.log (1233 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1233 / 640) = -Real.log (640 / 1233) := by
    rw [show ((1233 / 640) : ℝ) = ((640 / 1233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (652830143 / 250000000) ≤ -Real.log (47 / 640) ∧
    -Real.log (47 / 640) ≤ (10200471 / 3906250) := by
  have h := checkLog_sound (w := (33 / 127)) (n := 12)
    (lo := (66484879 / 125000000)) (hi := (531879033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 47) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(80 / 47) = 1/(47 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-10200471 / 3906250) (-652830143 / 250000000) (Real.log (47 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (654966551 / 1000000000) ≤ -Real.log (12800 / 24641) ∧
    -Real.log (12800 / 24641) ≤ (81870819 / 125000000) := by
  have h := checkLog_sound (w := (11841 / 37441)) (n := 12)
    (lo := (654966551 / 1000000000)) (hi := (81870819 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24641 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24641 / 12800) = 1/(12800 / 24641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (654966551 / 1000000000) (81870819 / 125000000) (Real.log (24641 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24641 / 12800) = -Real.log (12800 / 24641) := by
    rw [show ((24641 / 12800) : ℝ) = ((12800 / 24641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2591309373 / 1000000000) ≤ -Real.log (959 / 12800) ∧
    -Real.log (959 / 12800) ≤ (2591309377 / 1000000000) := by
  have h := checkLog_sound (w := (641 / 2559)) (n := 12)
    (lo := (511867833 / 1000000000)) (hi := (255933917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 959) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 959) = 1/(959 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2591309377 / 1000000000) (-2591309373 / 1000000000) (Real.log (959 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (616873403 / 1000000000) ≤ -Real.log (320 / 593) ∧
    -Real.log (320 / 593) ≤ (154218351 / 250000000) := by
  have h := checkLog_sound (w := (273 / 913)) (n := 12)
    (lo := (616873403 / 1000000000)) (hi := (154218351 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(593 / 320) = 1/(320 / 593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (616873403 / 1000000000) (154218351 / 250000000) (Real.log (593 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (593 / 320) = -Real.log (320 / 593) := by
    rw [show ((593 / 320) : ℝ) = ((320 / 593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (119885837 / 62500000) ≤ -Real.log (47 / 320) ∧
    -Real.log (47 / 320) ≤ (383634679 / 200000000) := by
  have h := checkLog_sound (w := (33 / 127)) (n := 12)
    (lo := (66484879 / 125000000)) (hi := (531879033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 47) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(80 / 47) = 1/(47 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-383634679 / 200000000) (-119885837 / 62500000) (Real.log (47 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (307635047 / 500000000) ≤ -Real.log (6400 / 11841) ∧
    -Real.log (6400 / 11841) ≤ (123054019 / 200000000) := by
  have h := checkLog_sound (w := (5441 / 18241)) (n := 12)
    (lo := (307635047 / 500000000)) (hi := (123054019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11841 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11841 / 6400) = 1/(6400 / 11841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (307635047 / 500000000) (123054019 / 200000000) (Real.log (11841 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11841 / 6400) = -Real.log (6400 / 11841) := by
    rw [show ((11841 / 6400) : ℝ) = ((6400 / 11841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1898162193 / 1000000000) ≤ -Real.log (959 / 6400) ∧
    -Real.log (959 / 6400) ≤ (474540549 / 250000000) := by
  have h := checkLog_sound (w := (641 / 2559)) (n := 12)
    (lo := (511867833 / 1000000000)) (hi := (255933917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 959) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 959) = 1/(959 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-474540549 / 250000000) (-1898162193 / 1000000000) (Real.log (959 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (663175483 / 1000000000) ≤ -Real.log (500000 / 970473) ∧
    -Real.log (500000 / 970473) ≤ (165793871 / 250000000) := by
  have h := checkLog_sound (w := (470473 / 1470473)) (n := 12)
    (lo := (663175483 / 1000000000)) (hi := (165793871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((970473 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(970473 / 500000) = 1/(500000 / 970473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (663175483 / 1000000000) (165793871 / 250000000) (Real.log (970473 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (970473 / 500000) = -Real.log (500000 / 970473) := by
    rw [show ((970473 / 500000) : ℝ) = ((500000 / 970473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2829302997 / 1000000000) ≤ -Real.log (29527 / 500000) ∧
    -Real.log (29527 / 500000) ≤ (1414651501 / 500000000) := by
  have h := checkLog_sound (w := (1723 / 60777)) (n := 12)
    (lo := (56714277 / 1000000000)) (hi := (28357139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 29527) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 29527) = 1/(29527 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1414651501 / 500000000) (-2829302997 / 1000000000) (Real.log (29527 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (41482913 / 62500000) ≤ -Real.log (15625 / 30344) ∧
    -Real.log (15625 / 30344) ≤ (663726609 / 1000000000) := by
  have h := checkLog_sound (w := (14719 / 45969)) (n := 12)
    (lo := (41482913 / 62500000)) (hi := (663726609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30344 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30344 / 15625) = 1/(15625 / 30344) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (41482913 / 62500000) (663726609 / 1000000000) (Real.log (30344 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (30344 / 15625) = -Real.log (15625 / 30344) := by
    rw [show ((30344 / 15625) : ℝ) = ((15625 / 30344) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1423794083 / 500000000) ≤ -Real.log (906 / 15625) ∧
    -Real.log (906 / 15625) ≤ (2847588171 / 1000000000) := by
  have h := checkLog_sound (w := (1129 / 30121)) (n := 12)
    (lo := (37499723 / 500000000)) (hi := (74999447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14496) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 14496) = 1/(906 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2847588171 / 1000000000) (-1423794083 / 500000000) (Real.log (906 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (13251017 / 20000000) ≤ -Real.log (500000 / 969867) ∧
    -Real.log (500000 / 969867) ≤ (662550851 / 1000000000) := by
  have h := checkLog_sound (w := (469867 / 1469867)) (n := 12)
    (lo := (13251017 / 20000000)) (hi := (662550851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((969867 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(969867 / 500000) = 1/(500000 / 969867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (13251017 / 20000000) (662550851 / 1000000000) (Real.log (969867 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (969867 / 500000) = -Real.log (500000 / 969867) := by
    rw [show ((969867 / 500000) : ℝ) = ((500000 / 969867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2808987179 / 1000000000) ≤ -Real.log (30133 / 500000) ∧
    -Real.log (30133 / 500000) ≤ (175561699 / 62500000) := by
  have h := checkLog_sound (w := (1117 / 61383)) (n := 12)
    (lo := (36398459 / 1000000000)) (hi := (1819923 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 30133) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 30133) = 1/(30133 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-175561699 / 62500000) (-2808987179 / 1000000000) (Real.log (30133 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (663131173 / 1000000000) ≤ -Real.log (50000 / 97043) ∧
    -Real.log (50000 / 97043) ≤ (331565587 / 500000000) := by
  have h := checkLog_sound (w := (47043 / 147043)) (n := 12)
    (lo := (663131173 / 1000000000)) (hi := (331565587 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97043 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97043 / 50000) = 1/(50000 / 97043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (663131173 / 1000000000) (331565587 / 500000000) (Real.log (97043 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (97043 / 50000) = -Real.log (50000 / 97043) := by
    rw [show ((97043 / 50000) : ℝ) = ((50000 / 97043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1413923881 / 500000000) ≤ -Real.log (2957 / 50000) ∧
    -Real.log (2957 / 50000) ≤ (2827847767 / 1000000000) := by
  have h := checkLog_sound (w := (84 / 3041)) (n := 12)
    (lo := (27629521 / 500000000)) (hi := (55259043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2957) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125 / 2957) = 1/(2957 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2827847767 / 1000000000) (-1413923881 / 500000000) (Real.log (2957 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3492478479 / 1000000000) ≤ -Real.log (62500000000 / 2054206742981) ∧
    -Real.log (62500000000 / 2054206742981) ≤ (698495697 / 200000000) := by
  have h := checkLog_sound (w := (54206742981 / 4054206742981)) (n := 12)
    (lo := (26742579 / 1000000000)) (hi := (1337129 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2054206742981 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2054206742981 / 2000000000000) = 1/(62500000000 / 2054206742981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3492478479 / 1000000000) (698495697 / 200000000) (Real.log (2054206742981 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2054206742981 / 62500000000) = -Real.log (62500000000 / 2054206742981) := by
    rw [show ((2054206742981 / 62500000000) : ℝ) = ((62500000000 / 2054206742981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1755657387 / 500000000) ≤ -Real.log (500000000000 / 16746136865343) ∧
    -Real.log (500000000000 / 16746136865343) ≤ (175565739 / 50000000) := by
  have h := checkLog_sound (w := (746136865343 / 32746136865343)) (n := 12)
    (lo := (22789437 / 500000000)) (hi := (364631 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16746136865343 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(16746136865343 / 16000000000000) = 1/(500000000000 / 16746136865343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1755657387 / 500000000) (175565739 / 50000000) (Real.log (16746136865343 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (16746136865343 / 500000000000) = -Real.log (500000000000 / 16746136865343) := by
    rw [show ((16746136865343 / 500000000000) : ℝ) = ((500000000000 / 16746136865343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3471538029 / 1000000000) ≤ -Real.log (15625000000 / 502909497063) ∧
    -Real.log (15625000000 / 502909497063) ≤ (694307607 / 200000000) := by
  have h := checkLog_sound (w := (2909497063 / 1002909497063)) (n := 12)
    (lo := (5802129 / 1000000000)) (hi := (580213 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((502909497063 / 500000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(502909497063 / 500000000000) = 1/(15625000000 / 502909497063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (3471538029 / 1000000000) (694307607 / 200000000) (Real.log (502909497063 / 15625000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (502909497063 / 15625000000) = -Real.log (15625000000 / 502909497063) := by
    rw [show ((502909497063 / 15625000000) : ℝ) = ((15625000000 / 502909497063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (698195787 / 200000000) ≤ -Real.log (31250000000 / 1025564338857) ∧
    -Real.log (31250000000 / 1025564338857) ≤ (3490978941 / 1000000000) := by
  have h := checkLog_sound (w := (25564338857 / 2025564338857)) (n := 12)
    (lo := (5048607 / 200000000)) (hi := (6310759 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1025564338857 / 1000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1025564338857 / 1000000000000) = 1/(31250000000 / 1025564338857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (698195787 / 200000000) (3490978941 / 1000000000) (Real.log (1025564338857 / 31250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1025564338857 / 31250000000) = -Real.log (31250000000 / 1025564338857) := by
    rw [show ((1025564338857 / 31250000000) : ℝ) = ((31250000000 / 1025564338857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0147
