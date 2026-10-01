import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0032
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

theorem reflection_log_1_neg : (170187833 / 250000000) ≤ -Real.log (102400 / 202277) ∧
    -Real.log (102400 / 202277) ≤ (680751333 / 1000000000) := by
  have h := checkLog_sound (w := (99877 / 304677)) (n := 12)
    (lo := (170187833 / 250000000)) (hi := (680751333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202277 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202277 / 102400) = 1/(102400 / 202277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (170187833 / 250000000) (680751333 / 1000000000) (Real.log (202277 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202277 / 102400) = -Real.log (102400 / 202277) := by
    rw [show ((202277 / 102400) : ℝ) = ((102400 / 202277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (92585951 / 25000000) ≤ -Real.log (2523 / 102400) ∧
    -Real.log (2523 / 102400) ≤ (1851719023 / 500000000) := by
  have h := checkLog_sound (w := (677 / 5723)) (n := 12)
    (lo := (11885107 / 50000000)) (hi := (237702141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2523) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2523) = 1/(2523 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1851719023 / 500000000) (-92585951 / 25000000) (Real.log (2523 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (680657397 / 1000000000) ≤ -Real.log (51200 / 101129) ∧
    -Real.log (51200 / 101129) ≤ (340328699 / 500000000) := by
  have h := checkLog_sound (w := (49929 / 152329)) (n := 12)
    (lo := (680657397 / 1000000000)) (hi := (340328699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101129 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101129 / 51200) = 1/(51200 / 101129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (680657397 / 1000000000) (340328699 / 500000000) (Real.log (101129 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (101129 / 51200) = -Real.log (51200 / 101129) := by
    rw [show ((101129 / 51200) : ℝ) = ((51200 / 101129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3695935537 / 1000000000) ≤ -Real.log (1271 / 51200) ∧
    -Real.log (1271 / 51200) ≤ (3695935543 / 1000000000) := by
  have h := checkLog_sound (w := (329 / 2871)) (n := 12)
    (lo := (230199637 / 1000000000)) (hi := (115099819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1271) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1271) = 1/(1271 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3695935543 / 1000000000) (-3695935537 / 1000000000) (Real.log (1271 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (83524987 / 125000000) ≤ -Real.log (51200 / 99877) ∧
    -Real.log (51200 / 99877) ≤ (668199897 / 1000000000) := by
  have h := checkLog_sound (w := (48677 / 151077)) (n := 12)
    (lo := (83524987 / 125000000)) (hi := (668199897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99877 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99877 / 51200) = 1/(51200 / 99877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (83524987 / 125000000) (668199897 / 1000000000) (Real.log (99877 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99877 / 51200) = -Real.log (51200 / 99877) := by
    rw [show ((99877 / 51200) : ℝ) = ((51200 / 99877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (150514543 / 50000000) ≤ -Real.log (2523 / 51200) ∧
    -Real.log (2523 / 51200) ≤ (602058173 / 200000000) := by
  have h := checkLog_sound (w := (677 / 5723)) (n := 12)
    (lo := (11885107 / 50000000)) (hi := (237702141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2523) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2523) = 1/(2523 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-602058173 / 200000000) (-150514543 / 50000000) (Real.log (2523 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (167002411 / 250000000) ≤ -Real.log (25600 / 49929) ∧
    -Real.log (25600 / 49929) ≤ (133601929 / 200000000) := by
  have h := checkLog_sound (w := (24329 / 75529)) (n := 12)
    (lo := (167002411 / 250000000)) (hi := (133601929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49929 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49929 / 25600) = 1/(25600 / 49929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (167002411 / 250000000) (133601929 / 200000000) (Real.log (49929 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49929 / 25600) = -Real.log (25600 / 49929) := by
    rw [show ((49929 / 25600) : ℝ) = ((25600 / 49929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3002788357 / 1000000000) ≤ -Real.log (1271 / 25600) ∧
    -Real.log (1271 / 25600) ≤ (1501394181 / 500000000) := by
  have h := checkLog_sound (w := (329 / 2871)) (n := 12)
    (lo := (230199637 / 1000000000)) (hi := (115099819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1271) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1271) = 1/(1271 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1501394181 / 500000000) (-3002788357 / 1000000000) (Real.log (1271 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (341313013 / 500000000) ≤ -Real.log (250000 / 494767) ∧
    -Real.log (250000 / 494767) ≤ (682626027 / 1000000000) := by
  have h := checkLog_sound (w := (244767 / 744767)) (n := 12)
    (lo := (341313013 / 500000000)) (hi := (682626027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((494767 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(494767 / 250000) = 1/(250000 / 494767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (341313013 / 500000000) (682626027 / 1000000000) (Real.log (494767 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (494767 / 250000) = -Real.log (250000 / 494767) := by
    rw [show ((494767 / 250000) : ℝ) = ((250000 / 494767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3866476187 / 1000000000) ≤ -Real.log (5233 / 250000) ∧
    -Real.log (5233 / 250000) ≤ (3866476193 / 1000000000) := by
  have h := checkLog_sound (w := (5159 / 26091)) (n := 12)
    (lo := (400740287 / 1000000000)) (hi := (6261567 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10466) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10466) = 1/(5233 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3866476193 / 1000000000) (-3866476187 / 1000000000) (Real.log (5233 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (341351161 / 500000000) ≤ -Real.log (1000000 / 1979219) ∧
    -Real.log (1000000 / 1979219) ≤ (682702323 / 1000000000) := by
  have h := checkLog_sound (w := (979219 / 2979219)) (n := 12)
    (lo := (341351161 / 500000000)) (hi := (682702323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979219 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979219 / 1000000) = 1/(1000000 / 1979219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (341351161 / 500000000) (682702323 / 1000000000) (Real.log (1979219 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1979219 / 1000000) = -Real.log (1000000 / 1979219) := by
    rw [show ((1979219 / 1000000) : ℝ) = ((1000000 / 1979219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (484214521 / 125000000) ≤ -Real.log (20781 / 1000000) ∧
    -Real.log (20781 / 1000000) ≤ (1936858087 / 500000000) := by
  have h := checkLog_sound (w := (10469 / 52031)) (n := 12)
    (lo := (101995067 / 250000000)) (hi := (407980269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20781) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 20781) = 1/(20781 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1936858087 / 500000000) (-484214521 / 125000000) (Real.log (20781 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (85321937 / 125000000) ≤ -Real.log (125000 / 247371) ∧
    -Real.log (125000 / 247371) ≤ (682575497 / 1000000000) := by
  have h := checkLog_sound (w := (122371 / 372371)) (n := 12)
    (lo := (85321937 / 125000000)) (hi := (682575497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247371 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247371 / 125000) = 1/(125000 / 247371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (85321937 / 125000000) (682575497 / 1000000000) (Real.log (247371 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (247371 / 125000) = -Real.log (125000 / 247371) := by
    rw [show ((247371 / 125000) : ℝ) = ((125000 / 247371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (965427547 / 250000000) ≤ -Real.log (2629 / 125000) ∧
    -Real.log (2629 / 125000) ≤ (1930855097 / 500000000) := by
  have h := checkLog_sound (w := (5109 / 26141)) (n := 12)
    (lo := (24748393 / 62500000)) (hi := (395974289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10516) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10516) = 1/(2629 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1930855097 / 500000000) (-965427547 / 250000000) (Real.log (2629 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (341326403 / 500000000) ≤ -Real.log (1000000 / 1979121) ∧
    -Real.log (1000000 / 1979121) ≤ (682652807 / 1000000000) := by
  have h := checkLog_sound (w := (979121 / 2979121)) (n := 12)
    (lo := (341326403 / 500000000)) (hi := (682652807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979121 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979121 / 1000000) = 1/(1000000 / 1979121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (341326403 / 500000000) (682652807 / 1000000000) (Real.log (1979121 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1979121 / 1000000) = -Real.log (1000000 / 1979121) := by
    rw [show ((1979121 / 1000000) : ℝ) = ((1000000 / 1979121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3869011407 / 1000000000) ≤ -Real.log (20879 / 1000000) ∧
    -Real.log (20879 / 1000000) ≤ (3869011413 / 1000000000) := by
  have h := checkLog_sound (w := (10371 / 52129)) (n := 12)
    (lo := (403275507 / 1000000000)) (hi := (100818877 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20879) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 20879) = 1/(20879 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3869011413 / 1000000000) (-3869011407 / 1000000000) (Real.log (20879 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4549102213 / 1000000000) ≤ -Real.log (31250000000 / 2954608971909) ∧
    -Real.log (31250000000 / 2954608971909) ≤ (227455111 / 50000000) := by
  have h := checkLog_sound (w := (954608971909 / 4954608971909)) (n := 12)
    (lo := (390219133 / 1000000000)) (hi := (195109567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2954608971909 / 2000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(2954608971909 / 2000000000000) = 1/(31250000000 / 2954608971909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4549102213 / 1000000000) (227455111 / 50000000) (Real.log (2954608971909 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2954608971909 / 31250000000) = -Real.log (31250000000 / 2954608971909) := by
    rw [show ((2954608971909 / 31250000000) : ℝ) = ((31250000000 / 2954608971909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (455641849 / 100000000) ≤ -Real.log (6250000000 / 595260995621) ∧
    -Real.log (6250000000 / 595260995621) ≤ (4556418497 / 1000000000) := by
  have h := checkLog_sound (w := (195260995621 / 995260995621)) (n := 12)
    (lo := (39753541 / 100000000)) (hi := (397535411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595260995621 / 400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(595260995621 / 400000000000) = 1/(6250000000 / 595260995621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (455641849 / 100000000) (4556418497 / 1000000000) (Real.log (595260995621 / 6250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (595260995621 / 6250000000) = -Real.log (6250000000 / 595260995621) := by
    rw [show ((595260995621 / 6250000000) : ℝ) = ((6250000000 / 595260995621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1136071421 / 250000000) ≤ -Real.log (400000000 / 37637276531) ∧
    -Real.log (400000000 / 37637276531) ≤ (4544285691 / 1000000000) := by
  have h := checkLog_sound (w := (12037276531 / 63237276531)) (n := 12)
    (lo := (96350651 / 250000000)) (hi := (77080521 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37637276531 / 25600000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(37637276531 / 25600000000) = 1/(400000000 / 37637276531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1136071421 / 250000000) (4544285691 / 1000000000) (Real.log (37637276531 / 400000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (37637276531 / 400000000) = -Real.log (400000000 / 37637276531) := by
    rw [show ((37637276531 / 400000000) : ℝ) = ((400000000 / 37637276531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4551664213 / 1000000000) ≤ -Real.log (50000000000 / 4739501412903) ∧
    -Real.log (50000000000 / 4739501412903) ≤ (227583211 / 50000000) := by
  have h := checkLog_sound (w := (1539501412903 / 7939501412903)) (n := 12)
    (lo := (392781133 / 1000000000)) (hi := (196390567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4739501412903 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4739501412903 / 3200000000000) = 1/(50000000000 / 4739501412903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4551664213 / 1000000000) (227583211 / 50000000) (Real.log (4739501412903 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4739501412903 / 50000000000) = -Real.log (50000000000 / 4739501412903) := by
    rw [show ((4739501412903 / 50000000000) : ℝ) = ((50000000000 / 4739501412903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0032
