import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0026
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

theorem reflection_log_1_neg : (681314757 / 1000000000) ≤ -Real.log (102400 / 202391) ∧
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


theorem reflection_log_1 : Bounds (681314757 / 1000000000) (340657379 / 500000000) (Real.log (202391 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202391 / 102400) = -Real.log (102400 / 202391) := by
    rw [show ((202391 / 102400) : ℝ) = ((102400 / 202391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1874837493 / 500000000) ≤ -Real.log (2409 / 102400) ∧
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


theorem reflection_log_2 : Bounds (-234354687 / 62500000) (-1874837493 / 500000000) (Real.log (2409 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (5449767 / 8000000) ≤ -Real.log (25600 / 50593) ∧
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


theorem reflection_log_3 : Bounds (5449767 / 8000000) (170305219 / 250000000) (Real.log (50593 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50593 / 25600) = -Real.log (25600 / 50593) := by
    rw [show ((50593 / 25600) : ℝ) = ((25600 / 50593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (935454709 / 250000000) ≤ -Real.log (607 / 25600) ∧
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


theorem reflection_log_4 : Bounds (-1870909421 / 500000000) (-935454709 / 250000000) (Real.log (607 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (669340649 / 1000000000) ≤ -Real.log (51200 / 99991) ∧
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


theorem reflection_log_5 : Bounds (669340649 / 1000000000) (13386813 / 20000000) (Real.log (99991 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99991 / 51200) = -Real.log (51200 / 99991) := by
    rw [show ((99991 / 51200) : ℝ) = ((51200 / 99991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1528263903 / 500000000) ≤ -Real.log (2409 / 51200) ∧
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


theorem reflection_log_6 : Bounds (-3056527811 / 1000000000) (-1528263903 / 500000000) (Real.log (2409 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (334575307 / 500000000) ≤ -Real.log (12800 / 24993) ∧
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


theorem reflection_log_7 : Bounds (334575307 / 500000000) (133830123 / 200000000) (Real.log (24993 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24993 / 12800) = -Real.log (12800 / 24993) := by
    rw [show ((24993 / 12800) : ℝ) = ((12800 / 24993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (381083957 / 125000000) ≤ -Real.log (607 / 12800) ∧
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


theorem reflection_log_8 : Bounds (-3048671661 / 1000000000) (-381083957 / 125000000) (Real.log (607 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (341540341 / 500000000) ≤ -Real.log (15625 / 30937) ∧
    -Real.log (15625 / 30937) ≤ (683080683 / 1000000000) := by
  have h := checkLog_sound (w := (7656 / 23281)) (n := 12)
    (lo := (341540341 / 500000000)) (hi := (683080683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30937 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30937 / 15625) = 1/(15625 / 30937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (341540341 / 500000000) (683080683 / 1000000000) (Real.log (30937 / 15625)) := by
  have h := reflection_log_9_neg
  have he : Real.log (30937 / 15625) = -Real.log (15625 / 30937) := by
    rw [show ((30937 / 15625) : ℝ) = ((15625 / 30937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3910424281 / 1000000000) ≤ -Real.log (313 / 15625) ∧
    -Real.log (313 / 15625) ≤ (3910424287 / 1000000000) := by
  have h := checkLog_sound (w := (5609 / 25641)) (n := 12)
    (lo := (444688381 / 1000000000)) (hi := (222344191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10016) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10016) = 1/(313 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3910424287 / 1000000000) (-3910424281 / 1000000000) (Real.log (313 / 15625)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (683156943 / 1000000000) ≤ -Real.log (1000000 / 1980119) ∧
    -Real.log (1000000 / 1980119) ≤ (42697309 / 62500000) := by
  have h := checkLog_sound (w := (980119 / 2980119)) (n := 12)
    (lo := (683156943 / 1000000000)) (hi := (42697309 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980119 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980119 / 1000000) = 1/(1000000 / 1980119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (683156943 / 1000000000) (42697309 / 62500000) (Real.log (1980119 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1980119 / 1000000) = -Real.log (1000000 / 1980119) := by
    rw [show ((1980119 / 1000000) : ℝ) = ((1000000 / 1980119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1958995387 / 500000000) ≤ -Real.log (19881 / 1000000) ∧
    -Real.log (19881 / 1000000) ≤ (195899539 / 50000000) := by
  have h := checkLog_sound (w := (11369 / 51131)) (n := 12)
    (lo := (226127437 / 500000000)) (hi := (3618039 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19881) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19881) = 1/(19881 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-195899539 / 50000000) (-1958995387 / 500000000) (Real.log (19881 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (341517613 / 500000000) ≤ -Real.log (500000 / 989939) ∧
    -Real.log (500000 / 989939) ≤ (683035227 / 1000000000) := by
  have h := checkLog_sound (w := (489939 / 1489939)) (n := 12)
    (lo := (341517613 / 500000000)) (hi := (683035227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((989939 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(989939 / 500000) = 1/(500000 / 989939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (341517613 / 500000000) (683035227 / 1000000000) (Real.log (989939 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (989939 / 500000) = -Real.log (500000 / 989939) := by
    rw [show ((989939 / 500000) : ℝ) = ((500000 / 989939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (976485383 / 250000000) ≤ -Real.log (10061 / 500000) ∧
    -Real.log (10061 / 500000) ≤ (1952970769 / 500000000) := by
  have h := checkLog_sound (w := (2782 / 12843)) (n := 12)
    (lo := (6878213 / 15625000)) (hi := (440205633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10061) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 10061) = 1/(10061 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1952970769 / 500000000) (-976485383 / 250000000) (Real.log (10061 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (683112501 / 1000000000) ≤ -Real.log (1000000 / 1980031) ∧
    -Real.log (1000000 / 1980031) ≤ (341556251 / 500000000) := by
  have h := checkLog_sound (w := (980031 / 2980031)) (n := 12)
    (lo := (683112501 / 1000000000)) (hi := (341556251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980031 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980031 / 1000000) = 1/(1000000 / 1980031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (683112501 / 1000000000) (341556251 / 500000000) (Real.log (1980031 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1980031 / 1000000) = -Real.log (1000000 / 1980031) := by
    rw [show ((1980031 / 1000000) : ℝ) = ((1000000 / 1980031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (782714841 / 200000000) ≤ -Real.log (19969 / 1000000) ∧
    -Real.log (19969 / 1000000) ≤ (3913574211 / 1000000000) := by
  have h := checkLog_sound (w := (11281 / 51219)) (n := 12)
    (lo := (89567661 / 200000000)) (hi := (223919153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19969) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19969) = 1/(19969 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3913574211 / 1000000000) (-782714841 / 200000000) (Real.log (19969 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4593504963 / 1000000000) ≤ -Real.log (500000000000 / 49420127795527) ∧
    -Real.log (500000000000 / 49420127795527) ≤ (459350497 / 100000000) := by
  have h := checkLog_sound (w := (17420127795527 / 81420127795527)) (n := 12)
    (lo := (434621883 / 1000000000)) (hi := (108655471 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49420127795527 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(49420127795527 / 32000000000000) = 1/(500000000000 / 49420127795527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4593504963 / 1000000000) (459350497 / 100000000) (Real.log (49420127795527 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (49420127795527 / 500000000000) = -Real.log (500000000000 / 49420127795527) := by
    rw [show ((49420127795527 / 500000000000) : ℝ) = ((500000000000 / 49420127795527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4601147717 / 1000000000) ≤ -Real.log (250000000000 / 24899640360143) ∧
    -Real.log (250000000000 / 24899640360143) ≤ (1150286931 / 250000000) := by
  have h := checkLog_sound (w := (8899640360143 / 40899640360143)) (n := 12)
    (lo := (442264637 / 1000000000)) (hi := (221132319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24899640360143 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(24899640360143 / 16000000000000) = 1/(250000000000 / 24899640360143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4601147717 / 1000000000) (1150286931 / 250000000) (Real.log (24899640360143 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (24899640360143 / 250000000000) = -Real.log (250000000000 / 24899640360143) := by
    rw [show ((24899640360143 / 250000000000) : ℝ) = ((250000000000 / 24899640360143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2294488379 / 500000000) ≤ -Real.log (500000000000 / 49196849219759) ∧
    -Real.log (500000000000 / 49196849219759) ≤ (917795353 / 200000000) := by
  have h := checkLog_sound (w := (17196849219759 / 81196849219759)) (n := 12)
    (lo := (215046839 / 500000000)) (hi := (430093679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49196849219759 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(49196849219759 / 32000000000000) = 1/(500000000000 / 49196849219759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2294488379 / 500000000) (917795353 / 200000000) (Real.log (49196849219759 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (49196849219759 / 500000000000) = -Real.log (500000000000 / 49196849219759) := by
    rw [show ((49196849219759 / 500000000000) : ℝ) = ((500000000000 / 49196849219759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (919337341 / 200000000) ≤ -Real.log (500000000000 / 49577620311483) ∧
    -Real.log (500000000000 / 49577620311483) ≤ (574585839 / 125000000) := by
  have h := checkLog_sound (w := (17577620311483 / 81577620311483)) (n := 12)
    (lo := (3502429 / 8000000)) (hi := (218901813 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49577620311483 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(49577620311483 / 32000000000000) = 1/(500000000000 / 49577620311483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (919337341 / 200000000) (574585839 / 125000000) (Real.log (49577620311483 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (49577620311483 / 500000000000) = -Real.log (500000000000 / 49577620311483) := by
    rw [show ((49577620311483 / 500000000000) : ℝ) = ((500000000000 / 49577620311483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0026
