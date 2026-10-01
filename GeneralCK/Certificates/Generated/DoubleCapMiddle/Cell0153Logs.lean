import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0153
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

theorem reflection_log_1_neg : (57575473 / 200000000) ≤ -Real.log (1280 / 1707) ∧
    -Real.log (1280 / 1707) ≤ (143938683 / 500000000) := by
  have h := checkLog_sound (w := (427 / 2987)) (n := 12)
    (lo := (57575473 / 200000000)) (hi := (143938683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1707 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1707 / 1280) = 1/(1280 / 1707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (57575473 / 200000000) (143938683 / 500000000) (Real.log (1707 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1707 / 1280) = -Real.log (1280 / 1707) := by
    rw [show ((1707 / 1280) : ℝ) = ((1280 / 1707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (405855809 / 1000000000) ≤ -Real.log (853 / 1280) ∧
    -Real.log (853 / 1280) ≤ (40585581 / 100000000) := by
  have h := checkLog_sound (w := (427 / 2133)) (n := 12)
    (lo := (405855809 / 1000000000)) (hi := (40585581 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 853) = 1/(853 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-40585581 / 100000000) (-405855809 / 1000000000) (Real.log (853 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (71749561 / 250000000) ≤ -Real.log (2560 / 3411) ∧
    -Real.log (2560 / 3411) ≤ (57399649 / 200000000) := by
  have h := checkLog_sound (w := (851 / 5971)) (n := 12)
    (lo := (71749561 / 250000000)) (hi := (57399649 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3411 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3411 / 2560) = 1/(2560 / 3411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (71749561 / 250000000) (57399649 / 200000000) (Real.log (3411 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3411 / 2560) = -Real.log (2560 / 3411) := by
    rw [show ((3411 / 2560) : ℝ) = ((2560 / 3411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (202049427 / 500000000) ≤ -Real.log (1709 / 2560) ∧
    -Real.log (1709 / 2560) ≤ (80819771 / 200000000) := by
  have h := checkLog_sound (w := (851 / 4269)) (n := 12)
    (lo := (202049427 / 500000000)) (hi := (80819771 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1709) = 1/(1709 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-80819771 / 200000000) (-202049427 / 500000000) (Real.log (1709 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (255569037 / 500000000) ≤ -Real.log (640 / 1067) ∧
    -Real.log (640 / 1067) ≤ (20445523 / 40000000) := by
  have h := checkLog_sound (w := (427 / 1707)) (n := 12)
    (lo := (255569037 / 500000000)) (hi := (20445523 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1067 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1067 / 640) = 1/(640 / 1067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (255569037 / 500000000) (20445523 / 40000000) (Real.log (1067 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1067 / 640) = -Real.log (640 / 1067) := by
    rw [show ((1067 / 640) : ℝ) = ((640 / 1067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (110017601 / 100000000) ≤ -Real.log (213 / 640) ∧
    -Real.log (213 / 640) ≤ (275044003 / 250000000) := by
  have h := checkLog_sound (w := (107 / 533)) (n := 12)
    (lo := (40702883 / 100000000)) (hi := (407028831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 213) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 213) = 1/(213 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-275044003 / 250000000) (-110017601 / 100000000) (Real.log (213 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (20389251 / 40000000) ≤ -Real.log (1280 / 2131) ∧
    -Real.log (1280 / 2131) ≤ (127432819 / 250000000) := by
  have h := checkLog_sound (w := (851 / 3411)) (n := 12)
    (lo := (20389251 / 40000000)) (hi := (127432819 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2131 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2131 / 1280) = 1/(1280 / 2131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (20389251 / 40000000) (127432819 / 250000000) (Real.log (2131 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2131 / 1280) = -Real.log (1280 / 2131) := by
    rw [show ((2131 / 1280) : ℝ) = ((1280 / 2131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1093158437 / 1000000000) ≤ -Real.log (429 / 1280) ∧
    -Real.log (429 / 1280) ≤ (1093158439 / 1000000000) := by
  have h := checkLog_sound (w := (211 / 1069)) (n := 12)
    (lo := (400011257 / 1000000000)) (hi := (200005629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 429) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 429) = 1/(429 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1093158439 / 1000000000) (-1093158437 / 1000000000) (Real.log (429 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (78529867 / 200000000) ≤ -Real.log (1000000 / 1480899) ∧
    -Real.log (1000000 / 1480899) ≤ (49081167 / 125000000) := by
  have h := checkLog_sound (w := (480899 / 2480899)) (n := 12)
    (lo := (78529867 / 200000000)) (hi := (49081167 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1480899 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1480899 / 1000000) = 1/(1000000 / 1480899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (78529867 / 200000000) (49081167 / 125000000) (Real.log (1480899 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1480899 / 1000000) = -Real.log (1000000 / 1480899) := by
    rw [show ((1480899 / 1000000) : ℝ) = ((1000000 / 1480899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (655656809 / 1000000000) ≤ -Real.log (519101 / 1000000) ∧
    -Real.log (519101 / 1000000) ≤ (65565681 / 100000000) := by
  have h := checkLog_sound (w := (480899 / 1519101)) (n := 12)
    (lo := (655656809 / 1000000000)) (hi := (65565681 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 519101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 519101) = 1/(519101 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-65565681 / 100000000) (-655656809 / 1000000000) (Real.log (519101 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (196929677 / 500000000) ≤ -Real.log (250000 / 370673) ∧
    -Real.log (250000 / 370673) ≤ (78771871 / 200000000) := by
  have h := checkLog_sound (w := (120673 / 620673)) (n := 12)
    (lo := (196929677 / 500000000)) (hi := (78771871 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((370673 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(370673 / 250000) = 1/(250000 / 370673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (196929677 / 500000000) (78771871 / 200000000) (Real.log (370673 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (370673 / 250000) = -Real.log (250000 / 370673) := by
    rw [show ((370673 / 250000) : ℝ) = ((250000 / 370673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (659116837 / 1000000000) ≤ -Real.log (129327 / 250000) ∧
    -Real.log (129327 / 250000) ≤ (329558419 / 500000000) := by
  have h := checkLog_sound (w := (120673 / 379327)) (n := 12)
    (lo := (659116837 / 1000000000)) (hi := (329558419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 129327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 129327) = 1/(129327 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-329558419 / 500000000) (-659116837 / 1000000000) (Real.log (129327 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (309854683 / 1000000000) ≤ -Real.log (1000000 / 1363227) ∧
    -Real.log (1000000 / 1363227) ≤ (77463671 / 250000000) := by
  have h := checkLog_sound (w := (363227 / 2363227)) (n := 12)
    (lo := (309854683 / 1000000000)) (hi := (77463671 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1363227 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1363227 / 1000000) = 1/(1000000 / 1363227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (309854683 / 1000000000) (77463671 / 250000000) (Real.log (1363227 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1363227 / 1000000) = -Real.log (1000000 / 1363227) := by
    rw [show ((1363227 / 1000000) : ℝ) = ((1000000 / 1363227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (112835511 / 250000000) ≤ -Real.log (636773 / 1000000) ∧
    -Real.log (636773 / 1000000) ≤ (90268409 / 200000000) := by
  have h := checkLog_sound (w := (363227 / 1636773)) (n := 12)
    (lo := (112835511 / 250000000)) (hi := (90268409 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 636773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 636773) = 1/(636773 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-90268409 / 200000000) (-112835511 / 250000000) (Real.log (636773 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (62196597 / 200000000) ≤ -Real.log (500000 / 682383) ∧
    -Real.log (500000 / 682383) ≤ (155491493 / 500000000) := by
  have h := checkLog_sound (w := (182383 / 1182383)) (n := 12)
    (lo := (62196597 / 200000000)) (hi := (155491493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((682383 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(682383 / 500000) = 1/(500000 / 682383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (62196597 / 200000000) (155491493 / 500000000) (Real.log (682383 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (682383 / 500000) = -Real.log (500000 / 682383) := by
    rw [show ((682383 / 500000) : ℝ) = ((500000 / 682383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (113440461 / 250000000) ≤ -Real.log (317617 / 500000) ∧
    -Real.log (317617 / 500000) ≤ (90752369 / 200000000) := by
  have h := checkLog_sound (w := (182383 / 817617)) (n := 12)
    (lo := (113440461 / 250000000)) (hi := (90752369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 317617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 317617) = 1/(317617 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-90752369 / 200000000) (-113440461 / 250000000) (Real.log (317617 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (32759567 / 31250000) ≤ -Real.log (20000000000 / 57056295403) ∧
    -Real.log (20000000000 / 57056295403) ≤ (524153073 / 500000000) := by
  have h := checkLog_sound (w := (17056295403 / 97056295403)) (n := 12)
    (lo := (88789741 / 250000000)) (hi := (71031793 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57056295403 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(57056295403 / 40000000000) = 1/(20000000000 / 57056295403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (32759567 / 31250000) (524153073 / 500000000) (Real.log (57056295403 / 20000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (57056295403 / 20000000000) = -Real.log (20000000000 / 57056295403) := by
    rw [show ((57056295403 / 20000000000) : ℝ) = ((20000000000 / 57056295403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1052976191 / 1000000000) ≤ -Real.log (500000000000 / 1433084352069) ∧
    -Real.log (500000000000 / 1433084352069) ≤ (1052976193 / 1000000000) := by
  have h := checkLog_sound (w := (433084352069 / 2433084352069)) (n := 12)
    (lo := (359829011 / 1000000000)) (hi := (89957253 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1433084352069 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1433084352069 / 1000000000000) = 1/(500000000000 / 1433084352069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1052976191 / 1000000000) (1052976193 / 1000000000) (Real.log (1433084352069 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1433084352069 / 500000000000) = -Real.log (500000000000 / 1433084352069) := by
    rw [show ((1433084352069 / 500000000000) : ℝ) = ((500000000000 / 1433084352069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (761196727 / 1000000000) ≤ -Real.log (250000000000 / 535209171871) ∧
    -Real.log (250000000000 / 535209171871) ≤ (761196729 / 1000000000) := by
  have h := checkLog_sound (w := (35209171871 / 1035209171871)) (n := 12)
    (lo := (68049547 / 1000000000)) (hi := (17012387 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((535209171871 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(535209171871 / 500000000000) = 1/(250000000000 / 535209171871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (761196727 / 1000000000) (761196729 / 1000000000) (Real.log (535209171871 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (535209171871 / 250000000000) = -Real.log (250000000000 / 535209171871) := by
    rw [show ((535209171871 / 250000000000) : ℝ) = ((250000000000 / 535209171871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (191186207 / 250000000) ≤ -Real.log (250000000000 / 537111521109) ∧
    -Real.log (250000000000 / 537111521109) ≤ (76474483 / 100000000) := by
  have h := checkLog_sound (w := (37111521109 / 1037111521109)) (n := 12)
    (lo := (4474853 / 62500000)) (hi := (71597649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((537111521109 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(537111521109 / 500000000000) = 1/(250000000000 / 537111521109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (191186207 / 250000000) (76474483 / 100000000) (Real.log (537111521109 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (537111521109 / 250000000000) = -Real.log (250000000000 / 537111521109) := by
    rw [show ((537111521109 / 250000000000) : ℝ) = ((250000000000 / 537111521109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0153
