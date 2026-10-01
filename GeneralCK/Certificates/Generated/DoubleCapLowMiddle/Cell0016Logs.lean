import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0016
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

theorem reflection_log_1_neg : (682253093 / 1000000000) ≤ -Real.log (102400 / 202581) ∧
    -Real.log (102400 / 202581) ≤ (341126547 / 500000000) := by
  have h := checkLog_sound (w := (100181 / 304981)) (n := 12)
    (lo := (682253093 / 1000000000)) (hi := (341126547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202581 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202581 / 102400) = 1/(102400 / 202581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (682253093 / 1000000000) (341126547 / 500000000) (Real.log (202581 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202581 / 102400) = -Real.log (102400 / 202581) := by
    rw [show ((202581 / 102400) : ℝ) = ((102400 / 202581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (766366013 / 200000000) ≤ -Real.log (2219 / 102400) ∧
    -Real.log (2219 / 102400) ≤ (3831830071 / 1000000000) := by
  have h := checkLog_sound (w := (981 / 5419)) (n := 12)
    (lo := (73218833 / 200000000)) (hi := (183047083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2219) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2219) = 1/(2219 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3831830071 / 1000000000) (-766366013 / 200000000) (Real.log (2219 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (682159299 / 1000000000) ≤ -Real.log (51200 / 101281) ∧
    -Real.log (51200 / 101281) ≤ (6821593 / 10000000) := by
  have h := checkLog_sound (w := (50081 / 152481)) (n := 12)
    (lo := (682159299 / 1000000000)) (hi := (6821593 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101281 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101281 / 51200) = 1/(51200 / 101281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (682159299 / 1000000000) (6821593 / 10000000) (Real.log (101281 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (101281 / 51200) = -Real.log (51200 / 101281) := by
    rw [show ((101281 / 51200) : ℝ) = ((51200 / 101281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3823304099 / 1000000000) ≤ -Real.log (1119 / 51200) ∧
    -Real.log (1119 / 51200) ≤ (764660821 / 200000000) := by
  have h := checkLog_sound (w := (481 / 2719)) (n := 12)
    (lo := (357568199 / 1000000000)) (hi := (1787841 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1119) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1119) = 1/(1119 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-764660821 / 200000000) (-3823304099 / 1000000000) (Real.log (1119 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (671239017 / 1000000000) ≤ -Real.log (51200 / 100181) ∧
    -Real.log (51200 / 100181) ≤ (335619509 / 500000000) := by
  have h := checkLog_sound (w := (48981 / 151381)) (n := 12)
    (lo := (671239017 / 1000000000)) (hi := (335619509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100181 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100181 / 51200) = 1/(51200 / 100181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (671239017 / 1000000000) (335619509 / 500000000) (Real.log (100181 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (100181 / 51200) = -Real.log (51200 / 100181) := by
    rw [show ((100181 / 51200) : ℝ) = ((51200 / 100181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (627736577 / 200000000) ≤ -Real.log (2219 / 51200) ∧
    -Real.log (2219 / 51200) ≤ (313868289 / 100000000) := by
  have h := checkLog_sound (w := (981 / 5419)) (n := 12)
    (lo := (73218833 / 200000000)) (hi := (183047083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2219) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2219) = 1/(2219 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-313868289 / 100000000) (-627736577 / 200000000) (Real.log (2219 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (671049343 / 1000000000) ≤ -Real.log (25600 / 50081) ∧
    -Real.log (25600 / 50081) ≤ (5242573 / 7812500) := by
  have h := checkLog_sound (w := (24481 / 75681)) (n := 12)
    (lo := (671049343 / 1000000000)) (hi := (5242573 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50081 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50081 / 25600) = 1/(25600 / 50081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (671049343 / 1000000000) (5242573 / 7812500) (Real.log (50081 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (50081 / 25600) = -Real.log (25600 / 50081) := by
    rw [show ((50081 / 25600) : ℝ) = ((25600 / 50081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3130156919 / 1000000000) ≤ -Real.log (1119 / 25600) ∧
    -Real.log (1119 / 25600) ≤ (782539231 / 250000000) := by
  have h := checkLog_sound (w := (481 / 2719)) (n := 12)
    (lo := (357568199 / 1000000000)) (hi := (1787841 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1119) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1119) = 1/(1119 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-782539231 / 250000000) (-3130156919 / 1000000000) (Real.log (1119 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (683840507 / 1000000000) ≤ -Real.log (1000000 / 1981473) ∧
    -Real.log (1000000 / 1981473) ≤ (170960127 / 250000000) := by
  have h := checkLog_sound (w := (981473 / 2981473)) (n := 12)
    (lo := (683840507 / 1000000000)) (hi := (170960127 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981473 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981473 / 1000000) = 1/(1000000 / 1981473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (683840507 / 1000000000) (170960127 / 250000000) (Real.log (1981473 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1981473 / 1000000) = -Real.log (1000000 / 1981473) := by
    rw [show ((1981473 / 1000000) : ℝ) = ((1000000 / 1981473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (997131537 / 250000000) ≤ -Real.log (18527 / 1000000) ∧
    -Real.log (18527 / 1000000) ≤ (1994263077 / 500000000) := by
  have h := checkLog_sound (w := (12723 / 49777)) (n := 12)
    (lo := (65348781 / 125000000)) (hi := (522790249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18527) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 18527) = 1/(18527 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1994263077 / 500000000) (-997131537 / 250000000) (Real.log (18527 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (136783443 / 200000000) ≤ -Real.log (8000 / 15853) ∧
    -Real.log (8000 / 15853) ≤ (21372413 / 31250000) := by
  have h := checkLog_sound (w := (7853 / 23853)) (n := 12)
    (lo := (136783443 / 200000000)) (hi := (21372413 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15853 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15853 / 8000) = 1/(8000 / 15853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (136783443 / 200000000) (21372413 / 31250000) (Real.log (15853 / 8000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (15853 / 8000) = -Real.log (8000 / 15853) := by
    rw [show ((15853 / 8000) : ℝ) = ((8000 / 15853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3996764231 / 1000000000) ≤ -Real.log (147 / 8000) ∧
    -Real.log (147 / 8000) ≤ (3996764237 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 397)) (n := 12)
    (lo := (531028331 / 1000000000)) (hi := (132757083 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 147) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(250 / 147) = 1/(147 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3996764237 / 1000000000) (-3996764231 / 1000000000) (Real.log (147 / 8000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (21368833 / 31250000) ≤ -Real.log (500000 / 990699) ∧
    -Real.log (500000 / 990699) ≤ (683802657 / 1000000000) := by
  have h := checkLog_sound (w := (490699 / 1490699)) (n := 12)
    (lo := (21368833 / 31250000)) (hi := (683802657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990699 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990699 / 500000) = 1/(500000 / 990699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (21368833 / 31250000) (683802657 / 1000000000) (Real.log (990699 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (990699 / 500000) = -Real.log (500000 / 990699) := by
    rw [show ((990699 / 500000) : ℝ) = ((500000 / 990699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1992243087 / 500000000) ≤ -Real.log (9301 / 500000) ∧
    -Real.log (9301 / 500000) ≤ (199224309 / 50000000) := by
  have h := checkLog_sound (w := (3162 / 12463)) (n := 12)
    (lo := (259375137 / 500000000)) (hi := (20750011 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9301) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9301) = 1/(9301 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-199224309 / 50000000) (-1992243087 / 500000000) (Real.log (9301 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (85485047 / 125000000) ≤ -Real.log (62500 / 123847) ∧
    -Real.log (62500 / 123847) ≤ (683880377 / 1000000000) := by
  have h := checkLog_sound (w := (61347 / 186347)) (n := 12)
    (lo := (85485047 / 125000000)) (hi := (683880377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123847 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123847 / 62500) = 1/(62500 / 123847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (85485047 / 125000000) (683880377 / 1000000000) (Real.log (123847 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (123847 / 62500) = -Real.log (62500 / 123847) := by
    rw [show ((123847 / 62500) : ℝ) = ((62500 / 123847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (249549957 / 62500000) ≤ -Real.log (1153 / 62500) ∧
    -Real.log (1153 / 62500) ≤ (1996399659 / 500000000) := by
  have h := checkLog_sound (w := (6401 / 24849)) (n := 12)
    (lo := (131765853 / 250000000)) (hi := (527063413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9224) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9224) = 1/(1153 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1996399659 / 500000000) (-249549957 / 62500000) (Real.log (1153 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (934473331 / 200000000) ≤ -Real.log (50000000000 / 5347527932207) ∧
    -Real.log (50000000000 / 5347527932207) ≤ (2336183331 / 500000000) := by
  have h := checkLog_sound (w := (2147527932207 / 8547527932207)) (n := 12)
    (lo := (20539343 / 40000000)) (hi := (64185447 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5347527932207 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5347527932207 / 3200000000000) = 1/(50000000000 / 5347527932207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (934473331 / 200000000) (2336183331 / 500000000) (Real.log (5347527932207 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5347527932207 / 50000000000) = -Real.log (50000000000 / 5347527932207) := by
    rw [show ((5347527932207 / 50000000000) : ℝ) = ((50000000000 / 5347527932207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (936136289 / 200000000) ≤ -Real.log (500000000000 / 53921768707483) ∧
    -Real.log (500000000000 / 53921768707483) ≤ (1170170363 / 250000000) := by
  have h := checkLog_sound (w := (21921768707483 / 85921768707483)) (n := 12)
    (lo := (104359673 / 200000000)) (hi := (260899183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53921768707483 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(53921768707483 / 32000000000000) = 1/(500000000000 / 53921768707483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (936136289 / 200000000) (1170170363 / 250000000) (Real.log (53921768707483 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (53921768707483 / 500000000000) = -Real.log (500000000000 / 53921768707483) := by
    rw [show ((53921768707483 / 500000000000) : ℝ) = ((500000000000 / 53921768707483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4668288829 / 1000000000) ≤ -Real.log (62500000000 / 6657207558327) ∧
    -Real.log (62500000000 / 6657207558327) ≤ (1167072209 / 250000000) := by
  have h := checkLog_sound (w := (2657207558327 / 10657207558327)) (n := 12)
    (lo := (509405749 / 1000000000)) (hi := (2037623 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6657207558327 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(6657207558327 / 4000000000000) = 1/(62500000000 / 6657207558327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4668288829 / 1000000000) (1167072209 / 250000000) (Real.log (6657207558327 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (6657207558327 / 62500000000) = -Real.log (62500000000 / 6657207558327) := by
    rw [show ((6657207558327 / 62500000000) : ℝ) = ((62500000000 / 6657207558327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (584584961 / 125000000) ≤ -Real.log (62500000000 / 6713302254987) ∧
    -Real.log (62500000000 / 6713302254987) ≤ (935335939 / 200000000) := by
  have h := checkLog_sound (w := (2713302254987 / 10713302254987)) (n := 12)
    (lo := (2022643 / 3906250)) (hi := (517796609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6713302254987 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(6713302254987 / 4000000000000) = 1/(62500000000 / 6713302254987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (584584961 / 125000000) (935335939 / 200000000) (Real.log (6713302254987 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (6713302254987 / 62500000000) = -Real.log (62500000000 / 6713302254987) := by
    rw [show ((6713302254987 / 62500000000) : ℝ) = ((62500000000 / 6713302254987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0016
