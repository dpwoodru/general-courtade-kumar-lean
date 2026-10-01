import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0022
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

theorem reflection_log_1_neg : (681690197 / 1000000000) ≤ -Real.log (102400 / 202467) ∧
    -Real.log (102400 / 202467) ≤ (340845099 / 500000000) := by
  have h := checkLog_sound (w := (100067 / 304867)) (n := 12)
    (lo := (681690197 / 1000000000)) (hi := (340845099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202467 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202467 / 102400) = 1/(102400 / 202467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (681690197 / 1000000000) (340845099 / 500000000) (Real.log (202467 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202467 / 102400) = -Real.log (102400 / 202467) := by
    rw [show ((202467 / 102400) : ℝ) = ((102400 / 202467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (945432929 / 250000000) ≤ -Real.log (2333 / 102400) ∧
    -Real.log (2333 / 102400) ≤ (1890865861 / 500000000) := by
  have h := checkLog_sound (w := (867 / 5533)) (n := 12)
    (lo := (39499477 / 125000000)) (hi := (315995817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2333) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2333) = 1/(2333 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1890865861 / 500000000) (-945432929 / 250000000) (Real.log (2333 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (13631927 / 20000000) ≤ -Real.log (6400 / 12653) ∧
    -Real.log (6400 / 12653) ≤ (681596351 / 1000000000) := by
  have h := checkLog_sound (w := (6253 / 19053)) (n := 12)
    (lo := (13631927 / 20000000)) (hi := (681596351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12653 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12653 / 6400) = 1/(6400 / 12653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (13631927 / 20000000) (681596351 / 1000000000) (Real.log (12653 / 6400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12653 / 6400) = -Real.log (6400 / 12653) := by
    rw [show ((12653 / 6400) : ℝ) = ((6400 / 12653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3773620679 / 1000000000) ≤ -Real.log (147 / 6400) ∧
    -Real.log (147 / 6400) ≤ (754724137 / 200000000) := by
  have h := checkLog_sound (w := (53 / 347)) (n := 12)
    (lo := (307884779 / 1000000000)) (hi := (15394239 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 147) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(200 / 147) = 1/(147 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-754724137 / 200000000) (-3773620679 / 1000000000) (Real.log (147 / 6400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (670100429 / 1000000000) ≤ -Real.log (51200 / 100067) ∧
    -Real.log (51200 / 100067) ≤ (67010043 / 100000000) := by
  have h := checkLog_sound (w := (48867 / 151267)) (n := 12)
    (lo := (670100429 / 1000000000)) (hi := (67010043 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100067 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100067 / 51200) = 1/(51200 / 100067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (670100429 / 1000000000) (67010043 / 100000000) (Real.log (100067 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (100067 / 51200) = -Real.log (51200 / 100067) := by
    rw [show ((100067 / 51200) : ℝ) = ((51200 / 100067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (386073067 / 125000000) ≤ -Real.log (2333 / 51200) ∧
    -Real.log (2333 / 51200) ≤ (3088584541 / 1000000000) := by
  have h := checkLog_sound (w := (867 / 5533)) (n := 12)
    (lo := (39499477 / 125000000)) (hi := (315995817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2333) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2333) = 1/(2333 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3088584541 / 1000000000) (-386073067 / 125000000) (Real.log (2333 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (334955269 / 500000000) ≤ -Real.log (3200 / 6253) ∧
    -Real.log (3200 / 6253) ≤ (669910539 / 1000000000) := by
  have h := checkLog_sound (w := (3053 / 9453)) (n := 12)
    (lo := (334955269 / 500000000)) (hi := (669910539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6253 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6253 / 3200) = 1/(3200 / 6253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (334955269 / 500000000) (669910539 / 1000000000) (Real.log (6253 / 3200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (6253 / 3200) = -Real.log (3200 / 6253) := by
    rw [show ((6253 / 3200) : ℝ) = ((3200 / 6253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3080473499 / 1000000000) ≤ -Real.log (147 / 3200) ∧
    -Real.log (147 / 3200) ≤ (96264797 / 31250000) := by
  have h := checkLog_sound (w := (53 / 347)) (n := 12)
    (lo := (307884779 / 1000000000)) (hi := (15394239 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 147) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(200 / 147) = 1/(147 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-96264797 / 31250000) (-3080473499 / 1000000000) (Real.log (147 / 3200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (683384177 / 1000000000) ≤ -Real.log (1000000 / 1980569) ∧
    -Real.log (1000000 / 1980569) ≤ (341692089 / 500000000) := by
  have h := checkLog_sound (w := (980569 / 2980569)) (n := 12)
    (lo := (683384177 / 1000000000)) (hi := (341692089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980569 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980569 / 1000000) = 1/(1000000 / 1980569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (683384177 / 1000000000) (341692089 / 500000000) (Real.log (1980569 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1980569 / 1000000) = -Real.log (1000000 / 1980569) := by
    rw [show ((1980569 / 1000000) : ℝ) = ((1000000 / 1980569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3940885547 / 1000000000) ≤ -Real.log (19431 / 1000000) ∧
    -Real.log (19431 / 1000000) ≤ (3940885553 / 1000000000) := by
  have h := checkLog_sound (w := (11819 / 50681)) (n := 12)
    (lo := (475149647 / 1000000000)) (hi := (29696853 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19431) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19431) = 1/(19431 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3940885553 / 1000000000) (-3940885547 / 1000000000) (Real.log (19431 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (341730207 / 500000000) ≤ -Real.log (12500 / 24759) ∧
    -Real.log (12500 / 24759) ≤ (136692083 / 200000000) := by
  have h := checkLog_sound (w := (12259 / 37259)) (n := 12)
    (lo := (341730207 / 500000000)) (hi := (136692083 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24759 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24759 / 12500) = 1/(12500 / 24759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (341730207 / 500000000) (136692083 / 200000000) (Real.log (24759 / 12500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (24759 / 12500) = -Real.log (12500 / 24759) := by
    rw [show ((24759 / 12500) : ℝ) = ((12500 / 24759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3948686987 / 1000000000) ≤ -Real.log (241 / 12500) ∧
    -Real.log (241 / 12500) ≤ (3948686993 / 1000000000) := by
  have h := checkLog_sound (w := (1197 / 5053)) (n := 12)
    (lo := (482951087 / 1000000000)) (hi := (30184443 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1928) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 1928) = 1/(241 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3948686993 / 1000000000) (-3948686987 / 1000000000) (Real.log (241 / 12500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (170835441 / 250000000) ≤ -Real.log (200000 / 396097) ∧
    -Real.log (200000 / 396097) ≤ (136668353 / 200000000) := by
  have h := checkLog_sound (w := (196097 / 596097)) (n := 12)
    (lo := (170835441 / 250000000)) (hi := (136668353 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((396097 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(396097 / 200000) = 1/(200000 / 396097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (170835441 / 250000000) (136668353 / 200000000) (Real.log (396097 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (396097 / 200000) = -Real.log (200000 / 396097) := by
    rw [show ((396097 / 200000) : ℝ) = ((200000 / 396097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1259703 / 320000) ≤ -Real.log (3903 / 200000) ∧
    -Real.log (3903 / 200000) ≤ (3936571881 / 1000000000) := by
  have h := checkLog_sound (w := (2347 / 10153)) (n := 12)
    (lo := (18833439 / 40000000)) (hi := (58854497 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3903) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 3903) = 1/(3903 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3936571881 / 1000000000) (-1259703 / 320000) (Real.log (3903 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (136683803 / 200000000) ≤ -Real.log (500000 / 990319) ∧
    -Real.log (500000 / 990319) ≤ (85427377 / 125000000) := by
  have h := checkLog_sound (w := (490319 / 1490319)) (n := 12)
    (lo := (136683803 / 200000000)) (hi := (85427377 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990319 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990319 / 500000) = 1/(500000 / 990319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (136683803 / 200000000) (85427377 / 125000000) (Real.log (990319 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (990319 / 500000) = -Real.log (500000 / 990319) := by
    rw [show ((990319 / 500000) : ℝ) = ((500000 / 990319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3944442893 / 1000000000) ≤ -Real.log (9681 / 500000) ∧
    -Real.log (9681 / 500000) ≤ (3944442899 / 1000000000) := by
  have h := checkLog_sound (w := (2972 / 12653)) (n := 12)
    (lo := (478706993 / 1000000000)) (hi := (239353497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9681) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9681) = 1/(9681 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3944442899 / 1000000000) (-3944442893 / 1000000000) (Real.log (9681 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4624269723 / 1000000000) ≤ -Real.log (125000000000 / 12741038803973) ∧
    -Real.log (125000000000 / 12741038803973) ≤ (462426973 / 100000000) := by
  have h := checkLog_sound (w := (4741038803973 / 20741038803973)) (n := 12)
    (lo := (465386643 / 1000000000)) (hi := (116346661 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12741038803973 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(12741038803973 / 8000000000000) = 1/(125000000000 / 12741038803973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4624269723 / 1000000000) (462426973 / 100000000) (Real.log (12741038803973 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (12741038803973 / 125000000000) = -Real.log (125000000000 / 12741038803973) := by
    rw [show ((12741038803973 / 125000000000) : ℝ) = ((125000000000 / 12741038803973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4632147401 / 1000000000) ≤ -Real.log (500000000000 / 51367219917013) ∧
    -Real.log (500000000000 / 51367219917013) ≤ (289509213 / 62500000) := by
  have h := checkLog_sound (w := (19367219917013 / 83367219917013)) (n := 12)
    (lo := (473264321 / 1000000000)) (hi := (236632161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51367219917013 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(51367219917013 / 32000000000000) = 1/(500000000000 / 51367219917013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4632147401 / 1000000000) (289509213 / 62500000) (Real.log (51367219917013 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (51367219917013 / 500000000000) = -Real.log (500000000000 / 51367219917013) := by
    rw [show ((51367219917013 / 500000000000) : ℝ) = ((500000000000 / 51367219917013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4619913639 / 1000000000) ≤ -Real.log (25000000000 / 2537131693569) ∧
    -Real.log (25000000000 / 2537131693569) ≤ (2309956823 / 500000000) := by
  have h := checkLog_sound (w := (937131693569 / 4137131693569)) (n := 12)
    (lo := (461030559 / 1000000000)) (hi := (2881441 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2537131693569 / 1600000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(2537131693569 / 1600000000000) = 1/(25000000000 / 2537131693569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4619913639 / 1000000000) (2309956823 / 500000000) (Real.log (2537131693569 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2537131693569 / 25000000000) = -Real.log (25000000000 / 2537131693569) := by
    rw [show ((2537131693569 / 25000000000) : ℝ) = ((25000000000 / 2537131693569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1156965477 / 250000000) ≤ -Real.log (500000000000 / 51147557070551) ∧
    -Real.log (500000000000 / 51147557070551) ≤ (925572383 / 200000000) := by
  have h := checkLog_sound (w := (19147557070551 / 83147557070551)) (n := 12)
    (lo := (117244707 / 250000000)) (hi := (468978829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51147557070551 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(51147557070551 / 32000000000000) = 1/(500000000000 / 51147557070551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1156965477 / 250000000) (925572383 / 200000000) (Real.log (51147557070551 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (51147557070551 / 500000000000) = -Real.log (500000000000 / 51147557070551) := by
    rw [show ((51147557070551 / 500000000000) : ℝ) = ((500000000000 / 51147557070551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0022
