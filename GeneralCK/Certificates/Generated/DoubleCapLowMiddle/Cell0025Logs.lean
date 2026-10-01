import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0025
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

theorem reflection_log_1_neg : (68140863 / 100000000) ≤ -Real.log (10240 / 20241) ∧
    -Real.log (10240 / 20241) ≤ (681408631 / 1000000000) := by
  have h := checkLog_sound (w := (10001 / 30481)) (n := 12)
    (lo := (68140863 / 100000000)) (hi := (681408631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20241 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20241 / 10240) = 1/(10240 / 20241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (68140863 / 100000000) (681408631 / 1000000000) (Real.log (20241 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (20241 / 10240) = -Real.log (10240 / 20241) := by
    rw [show ((20241 / 10240) : ℝ) = ((10240 / 20241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3757593343 / 1000000000) ≤ -Real.log (239 / 10240) ∧
    -Real.log (239 / 10240) ≤ (3757593349 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 559)) (n := 12)
    (lo := (291857443 / 1000000000)) (hi := (72964361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 239) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(320 / 239) = 1/(239 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3757593349 / 1000000000) (-3757593343 / 1000000000) (Real.log (239 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (681314757 / 1000000000) ≤ -Real.log (102400 / 202391) ∧
    -Real.log (102400 / 202391) ≤ (340657379 / 500000000) := by
  have h := checkLog_sound (w := (99991 / 304791)) (n := 12)
    (lo := (681314757 / 1000000000)) (hi := (340657379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202391 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202391 / 102400) = 1/(102400 / 202391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (681314757 / 1000000000) (340657379 / 500000000) (Real.log (202391 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202391 / 102400) = -Real.log (102400 / 202391) := by
    rw [show ((202391 / 102400) : ℝ) = ((102400 / 202391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1874837493 / 500000000) ≤ -Real.log (2409 / 102400) ∧
    -Real.log (2409 / 102400) ≤ (234354687 / 62500000) := by
  have h := checkLog_sound (w := (791 / 5609)) (n := 12)
    (lo := (141969543 / 500000000)) (hi := (283939087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2409) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2409) = 1/(2409 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-234354687 / 62500000) (-1874837493 / 500000000) (Real.log (2409 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (83691331 / 125000000) ≤ -Real.log (5120 / 10001) ∧
    -Real.log (5120 / 10001) ≤ (669530649 / 1000000000) := by
  have h := checkLog_sound (w := (4881 / 15121)) (n := 12)
    (lo := (83691331 / 125000000)) (hi := (669530649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001 / 5120) = 1/(5120 / 10001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (83691331 / 125000000) (669530649 / 1000000000) (Real.log (10001 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (10001 / 5120) = -Real.log (5120 / 10001) := by
    rw [show ((10001 / 5120) : ℝ) = ((5120 / 10001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3064446163 / 1000000000) ≤ -Real.log (239 / 5120) ∧
    -Real.log (239 / 5120) ≤ (383055771 / 125000000) := by
  have h := checkLog_sound (w := (81 / 559)) (n := 12)
    (lo := (291857443 / 1000000000)) (hi := (72964361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 239) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(320 / 239) = 1/(239 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-383055771 / 125000000) (-3064446163 / 1000000000) (Real.log (239 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (669340649 / 1000000000) ≤ -Real.log (51200 / 99991) ∧
    -Real.log (51200 / 99991) ≤ (13386813 / 20000000) := by
  have h := checkLog_sound (w := (48791 / 151191)) (n := 12)
    (lo := (669340649 / 1000000000)) (hi := (13386813 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99991 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99991 / 51200) = 1/(51200 / 99991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (669340649 / 1000000000) (13386813 / 20000000) (Real.log (99991 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99991 / 51200) = -Real.log (51200 / 99991) := by
    rw [show ((99991 / 51200) : ℝ) = ((51200 / 99991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1528263903 / 500000000) ≤ -Real.log (2409 / 51200) ∧
    -Real.log (2409 / 51200) ≤ (3056527811 / 1000000000) := by
  have h := checkLog_sound (w := (791 / 5609)) (n := 12)
    (lo := (141969543 / 500000000)) (hi := (283939087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2409) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2409) = 1/(2409 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-3056527811 / 1000000000) (-1528263903 / 500000000) (Real.log (2409 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (341578219 / 500000000) ≤ -Real.log (500000 / 990059) ∧
    -Real.log (500000 / 990059) ≤ (683156439 / 1000000000) := by
  have h := checkLog_sound (w := (490059 / 1490059)) (n := 12)
    (lo := (341578219 / 500000000)) (hi := (683156439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990059 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990059 / 500000) = 1/(500000 / 990059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (341578219 / 500000000) (683156439 / 1000000000) (Real.log (990059 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (990059 / 500000) = -Real.log (500000 / 990059) := by
    rw [show ((990059 / 500000) : ℝ) = ((500000 / 990059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (979485119 / 250000000) ≤ -Real.log (9941 / 500000) ∧
    -Real.log (9941 / 500000) ≤ (1958970241 / 500000000) := by
  have h := checkLog_sound (w := (2842 / 12783)) (n := 12)
    (lo := (14131393 / 31250000)) (hi := (452204577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9941) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9941) = 1/(9941 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1958970241 / 500000000) (-979485119 / 250000000) (Real.log (9941 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (341616347 / 500000000) ≤ -Real.log (1000000 / 1980269) ∧
    -Real.log (1000000 / 1980269) ≤ (136646539 / 200000000) := by
  have h := checkLog_sound (w := (980269 / 2980269)) (n := 12)
    (lo := (341616347 / 500000000)) (hi := (136646539 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980269 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980269 / 1000000) = 1/(1000000 / 1980269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (341616347 / 500000000) (136646539 / 200000000) (Real.log (1980269 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1980269 / 1000000) = -Real.log (1000000 / 1980269) := by
    rw [show ((1980269 / 1000000) : ℝ) = ((1000000 / 1980269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3925564273 / 1000000000) ≤ -Real.log (19731 / 1000000) ∧
    -Real.log (19731 / 1000000) ≤ (3925564279 / 1000000000) := by
  have h := checkLog_sound (w := (11519 / 50981)) (n := 12)
    (lo := (459828373 / 1000000000)) (hi := (229914187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19731) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19731) = 1/(19731 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3925564279 / 1000000000) (-3925564273 / 1000000000) (Real.log (19731 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (170777999 / 250000000) ≤ -Real.log (100000 / 198003) ∧
    -Real.log (100000 / 198003) ≤ (683111997 / 1000000000) := by
  have h := checkLog_sound (w := (98003 / 298003)) (n := 12)
    (lo := (170777999 / 250000000)) (hi := (683111997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198003 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198003 / 100000) = 1/(100000 / 198003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (170777999 / 250000000) (683111997 / 1000000000) (Real.log (198003 / 100000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (198003 / 100000) = -Real.log (100000 / 198003) := by
    rw [show ((198003 / 100000) : ℝ) = ((100000 / 198003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (122297629 / 31250000) ≤ -Real.log (1997 / 100000) ∧
    -Real.log (1997 / 100000) ≤ (1956762067 / 500000000) := by
  have h := checkLog_sound (w := (564 / 2561)) (n := 12)
    (lo := (111947057 / 250000000)) (hi := (447788229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1997) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 1997) = 1/(1997 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1956762067 / 500000000) (-122297629 / 31250000) (Real.log (1997 / 100000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (683188759 / 1000000000) ≤ -Real.log (500000 / 990091) ∧
    -Real.log (500000 / 990091) ≤ (17079719 / 25000000) := by
  have h := checkLog_sound (w := (490091 / 1490091)) (n := 12)
    (lo := (683188759 / 1000000000)) (hi := (17079719 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990091 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990091 / 500000) = 1/(500000 / 990091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (683188759 / 1000000000) (17079719 / 25000000) (Real.log (990091 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (990091 / 500000) = -Real.log (500000 / 990091) := by
    rw [show ((990091 / 500000) : ℝ) = ((500000 / 990091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (196058233 / 50000000) ≤ -Real.log (9909 / 500000) ∧
    -Real.log (9909 / 500000) ≤ (1960582333 / 500000000) := by
  have h := checkLog_sound (w := (2858 / 12767)) (n := 12)
    (lo := (11385719 / 25000000)) (hi := (455428761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9909) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9909) = 1/(9909 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1960582333 / 500000000) (-196058233 / 50000000) (Real.log (9909 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2300548457 / 500000000) ≤ -Real.log (62500000000 / 6224593853737) ∧
    -Real.log (62500000000 / 6224593853737) ≤ (4601096921 / 1000000000) := by
  have h := checkLog_sound (w := (2224593853737 / 10224593853737)) (n := 12)
    (lo := (221106917 / 500000000)) (hi := (88442767 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6224593853737 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(6224593853737 / 4000000000000) = 1/(62500000000 / 6224593853737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2300548457 / 500000000) (4601096921 / 1000000000) (Real.log (6224593853737 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6224593853737 / 62500000000) = -Real.log (62500000000 / 6224593853737) := by
    rw [show ((6224593853737 / 62500000000) : ℝ) = ((62500000000 / 6224593853737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2304398483 / 500000000) ≤ -Real.log (250000000000 / 25090834220263) ∧
    -Real.log (250000000000 / 25090834220263) ≤ (4608796973 / 1000000000) := by
  have h := checkLog_sound (w := (9090834220263 / 41090834220263)) (n := 12)
    (lo := (224956943 / 500000000)) (hi := (449913887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25090834220263 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(25090834220263 / 16000000000000) = 1/(250000000000 / 25090834220263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2304398483 / 500000000) (4608796973 / 1000000000) (Real.log (25090834220263 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (25090834220263 / 250000000000) = -Real.log (250000000000 / 25090834220263) := by
    rw [show ((25090834220263 / 250000000000) : ℝ) = ((250000000000 / 25090834220263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1149159031 / 250000000) ≤ -Real.log (500000000000 / 49575112669003) ∧
    -Real.log (500000000000 / 49575112669003) ≤ (4596636131 / 1000000000) := by
  have h := checkLog_sound (w := (17575112669003 / 81575112669003)) (n := 12)
    (lo := (109438261 / 250000000)) (hi := (87550609 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49575112669003 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(49575112669003 / 32000000000000) = 1/(500000000000 / 49575112669003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1149159031 / 250000000) (4596636131 / 1000000000) (Real.log (49575112669003 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (49575112669003 / 500000000000) = -Real.log (500000000000 / 49575112669003) := by
    rw [show ((49575112669003 / 500000000000) : ℝ) = ((500000000000 / 49575112669003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4604353419 / 1000000000) ≤ -Real.log (250000000000 / 24979589262287) ∧
    -Real.log (250000000000 / 24979589262287) ≤ (2302176713 / 500000000) := by
  have h := checkLog_sound (w := (8979589262287 / 40979589262287)) (n := 12)
    (lo := (445470339 / 1000000000)) (hi := (22273517 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24979589262287 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(24979589262287 / 16000000000000) = 1/(250000000000 / 24979589262287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4604353419 / 1000000000) (2302176713 / 500000000) (Real.log (24979589262287 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (24979589262287 / 250000000000) = -Real.log (250000000000 / 24979589262287) := by
    rw [show ((24979589262287 / 250000000000) : ℝ) = ((250000000000 / 24979589262287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0025
