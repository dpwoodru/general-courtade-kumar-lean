import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0027
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

theorem reflection_log_1_neg : (5449767 / 8000000) ≤ -Real.log (25600 / 50593) ∧
    -Real.log (25600 / 50593) ≤ (170305219 / 250000000) := by
  have h := checkLog_sound (w := (24993 / 76193)) (n := 12)
    (lo := (5449767 / 8000000)) (hi := (170305219 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50593 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50593 / 25600) = 1/(25600 / 50593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (5449767 / 8000000) (170305219 / 250000000) (Real.log (50593 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50593 / 25600) = -Real.log (25600 / 50593) := by
    rw [show ((50593 / 25600) : ℝ) = ((25600 / 50593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (935454709 / 250000000) ≤ -Real.log (607 / 25600) ∧
    -Real.log (607 / 25600) ≤ (1870909421 / 500000000) := by
  have h := checkLog_sound (w := (193 / 1407)) (n := 12)
    (lo := (34510367 / 125000000)) (hi := (276082937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 607) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(800 / 607) = 1/(607 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1870909421 / 500000000) (-935454709 / 250000000) (Real.log (607 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (85140873 / 125000000) ≤ -Real.log (102400 / 202353) ∧
    -Real.log (102400 / 202353) ≤ (136225397 / 200000000) := by
  have h := checkLog_sound (w := (99953 / 304753)) (n := 12)
    (lo := (85140873 / 125000000)) (hi := (136225397 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202353 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202353 / 102400) = 1/(102400 / 202353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (85140873 / 125000000) (136225397 / 200000000) (Real.log (202353 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202353 / 102400) = -Real.log (102400 / 202353) := by
    rw [show ((202353 / 102400) : ℝ) = ((102400 / 202353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (149360957 / 40000000) ≤ -Real.log (2447 / 102400) ∧
    -Real.log (2447 / 102400) ≤ (3734023931 / 1000000000) := by
  have h := checkLog_sound (w := (753 / 5647)) (n := 12)
    (lo := (10731521 / 40000000)) (hi := (134144013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2447) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2447) = 1/(2447 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3734023931 / 1000000000) (-149360957 / 40000000) (Real.log (2447 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (334575307 / 500000000) ≤ -Real.log (12800 / 24993) ∧
    -Real.log (12800 / 24993) ≤ (133830123 / 200000000) := by
  have h := checkLog_sound (w := (12193 / 37793)) (n := 12)
    (lo := (334575307 / 500000000)) (hi := (133830123 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24993 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24993 / 12800) = 1/(12800 / 24993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (334575307 / 500000000) (133830123 / 200000000) (Real.log (24993 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24993 / 12800) = -Real.log (12800 / 24993) := by
    rw [show ((24993 / 12800) : ℝ) = ((12800 / 24993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (381083957 / 125000000) ≤ -Real.log (607 / 12800) ∧
    -Real.log (607 / 12800) ≤ (3048671661 / 1000000000) := by
  have h := checkLog_sound (w := (193 / 1407)) (n := 12)
    (lo := (34510367 / 125000000)) (hi := (276082937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 607) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 607) = 1/(607 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3048671661 / 1000000000) (-381083957 / 125000000) (Real.log (607 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (668960543 / 1000000000) ≤ -Real.log (51200 / 99953) ∧
    -Real.log (51200 / 99953) ≤ (20905017 / 31250000) := by
  have h := checkLog_sound (w := (48753 / 151153)) (n := 12)
    (lo := (668960543 / 1000000000)) (hi := (20905017 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99953 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99953 / 51200) = 1/(51200 / 99953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (668960543 / 1000000000) (20905017 / 31250000) (Real.log (99953 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (99953 / 51200) = -Real.log (51200 / 99953) := by
    rw [show ((99953 / 51200) : ℝ) = ((51200 / 99953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (608175349 / 200000000) ≤ -Real.log (2447 / 51200) ∧
    -Real.log (2447 / 51200) ≤ (12163507 / 4000000) := by
  have h := checkLog_sound (w := (753 / 5647)) (n := 12)
    (lo := (10731521 / 40000000)) (hi := (134144013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2447) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2447) = 1/(2447 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-12163507 / 4000000) (-608175349 / 200000000) (Real.log (2447 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (1333993 / 1953125) ≤ -Real.log (1000000 / 1979817) ∧
    -Real.log (1000000 / 1979817) ≤ (683004417 / 1000000000) := by
  have h := checkLog_sound (w := (979817 / 2979817)) (n := 12)
    (lo := (1333993 / 1953125)) (hi := (683004417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979817 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979817 / 1000000) = 1/(1000000 / 1979817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (1333993 / 1953125) (683004417 / 1000000000) (Real.log (1979817 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1979817 / 1000000) = -Real.log (1000000 / 1979817) := by
    rw [show ((1979817 / 1000000) : ℝ) = ((1000000 / 1979817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (390291461 / 100000000) ≤ -Real.log (20183 / 1000000) ∧
    -Real.log (20183 / 1000000) ≤ (487864327 / 125000000) := by
  have h := checkLog_sound (w := (11067 / 51433)) (n := 12)
    (lo := (43717871 / 100000000)) (hi := (437178711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20183) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 20183) = 1/(20183 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-487864327 / 125000000) (-390291461 / 100000000) (Real.log (20183 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (170770297 / 250000000) ≤ -Real.log (1000000 / 1979969) ∧
    -Real.log (1000000 / 1979969) ≤ (683081189 / 1000000000) := by
  have h := checkLog_sound (w := (979969 / 2979969)) (n := 12)
    (lo := (170770297 / 250000000)) (hi := (683081189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979969 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979969 / 1000000) = 1/(1000000 / 1979969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (170770297 / 250000000) (683081189 / 1000000000) (Real.log (1979969 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1979969 / 1000000) = -Real.log (1000000 / 1979969) := by
    rw [show ((1979969 / 1000000) : ℝ) = ((1000000 / 1979969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1955237101 / 500000000) ≤ -Real.log (20031 / 1000000) ∧
    -Real.log (20031 / 1000000) ≤ (122202319 / 31250000) := by
  have h := checkLog_sound (w := (11219 / 51281)) (n := 12)
    (lo := (222369151 / 500000000)) (hi := (444738303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20031) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 20031) = 1/(20031 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-122202319 / 31250000) (-1955237101 / 500000000) (Real.log (20031 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (682958451 / 1000000000) ≤ -Real.log (500000 / 989863) ∧
    -Real.log (500000 / 989863) ≤ (170739613 / 250000000) := by
  have h := checkLog_sound (w := (489863 / 1489863)) (n := 12)
    (lo := (682958451 / 1000000000)) (hi := (170739613 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989863 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989863 / 500000) = 1/(500000 / 989863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (682958451 / 1000000000) (170739613 / 250000000) (Real.log (989863 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (989863 / 500000) = -Real.log (500000 / 989863) := by
    rw [show ((989863 / 500000) : ℝ) = ((500000 / 989863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3898415999 / 1000000000) ≤ -Real.log (10137 / 500000) ∧
    -Real.log (10137 / 500000) ≤ (779683201 / 200000000) := by
  have h := checkLog_sound (w := (2744 / 12881)) (n := 12)
    (lo := (432680099 / 1000000000)) (hi := (4326801 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10137) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10137) = 1/(10137 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-779683201 / 200000000) (-3898415999 / 1000000000) (Real.log (10137 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (683035731 / 1000000000) ≤ -Real.log (1000000 / 1979879) ∧
    -Real.log (1000000 / 1979879) ≤ (170758933 / 250000000) := by
  have h := checkLog_sound (w := (979879 / 2979879)) (n := 12)
    (lo := (683035731 / 1000000000)) (hi := (170758933 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1979879 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1979879 / 1000000) = 1/(1000000 / 1979879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (683035731 / 1000000000) (170758933 / 250000000) (Real.log (1979879 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1979879 / 1000000) = -Real.log (1000000 / 1979879) := by
    rw [show ((1979879 / 1000000) : ℝ) = ((1000000 / 1979879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (390599123 / 100000000) ≤ -Real.log (20121 / 1000000) ∧
    -Real.log (20121 / 1000000) ≤ (976497809 / 250000000) := by
  have h := checkLog_sound (w := (11129 / 51371)) (n := 12)
    (lo := (44025533 / 100000000)) (hi := (440255331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20121) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 20121) = 1/(20121 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-976497809 / 250000000) (-390599123 / 100000000) (Real.log (20121 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (183436761 / 40000000) ≤ -Real.log (500000000000 / 49046648169251) ∧
    -Real.log (500000000000 / 49046648169251) ≤ (573239879 / 125000000) := by
  have h := checkLog_sound (w := (17046648169251 / 81046648169251)) (n := 12)
    (lo := (85407189 / 200000000)) (hi := (213517973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49046648169251 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(49046648169251 / 32000000000000) = 1/(500000000000 / 49046648169251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (183436761 / 40000000) (573239879 / 125000000) (Real.log (49046648169251 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (49046648169251 / 500000000000) = -Real.log (500000000000 / 49046648169251) := by
    rw [show ((49046648169251 / 500000000000) : ℝ) = ((500000000000 / 49046648169251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (459355539 / 100000000) ≤ -Real.log (100000000000 / 9884523987819) ∧
    -Real.log (100000000000 / 9884523987819) ≤ (4593555397 / 1000000000) := by
  have h := checkLog_sound (w := (3484523987819 / 16284523987819)) (n := 12)
    (lo := (43467231 / 100000000)) (hi := (434672311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9884523987819 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(9884523987819 / 6400000000000) = 1/(100000000000 / 9884523987819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (459355539 / 100000000) (4593555397 / 1000000000) (Real.log (9884523987819 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (9884523987819 / 100000000000) = -Real.log (100000000000 / 9884523987819) := by
    rw [show ((9884523987819 / 100000000000) : ℝ) = ((100000000000 / 9884523987819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4581374449 / 1000000000) ≤ -Real.log (250000000000 / 24412128834961) ∧
    -Real.log (250000000000 / 24412128834961) ≤ (572671807 / 125000000) := by
  have h := checkLog_sound (w := (8412128834961 / 40412128834961)) (n := 12)
    (lo := (422491369 / 1000000000)) (hi := (42249137 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24412128834961 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(24412128834961 / 16000000000000) = 1/(250000000000 / 24412128834961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4581374449 / 1000000000) (572671807 / 125000000) (Real.log (24412128834961 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (24412128834961 / 250000000000) = -Real.log (250000000000 / 24412128834961) := by
    rw [show ((24412128834961 / 250000000000) : ℝ) = ((250000000000 / 24412128834961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4589026961 / 1000000000) ≤ -Real.log (500000000000 / 49199319119329) ∧
    -Real.log (500000000000 / 49199319119329) ≤ (573628371 / 125000000) := by
  have h := checkLog_sound (w := (17199319119329 / 81199319119329)) (n := 12)
    (lo := (430143881 / 1000000000)) (hi := (215071941 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49199319119329 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(49199319119329 / 32000000000000) = 1/(500000000000 / 49199319119329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4589026961 / 1000000000) (573628371 / 125000000) (Real.log (49199319119329 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (49199319119329 / 500000000000) = -Real.log (500000000000 / 49199319119329) := by
    rw [show ((49199319119329 / 500000000000) : ℝ) = ((500000000000 / 49199319119329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0027
