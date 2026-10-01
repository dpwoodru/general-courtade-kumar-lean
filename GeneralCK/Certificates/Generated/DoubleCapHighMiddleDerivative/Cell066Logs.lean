import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell066
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (254066713 / 1000000000) ≤ -Real.log (5120 / 6601) ∧
    -Real.log (5120 / 6601) ≤ (127033357 / 500000000) := by
  have h := checkLog_sound (w := (1481 / 11721)) (n := 12)
    (lo := (254066713 / 1000000000)) (hi := (127033357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6601 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6601 / 5120) = 1/(5120 / 6601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (254066713 / 1000000000) (127033357 / 500000000) (Real.log (6601 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6601 / 5120) = -Real.log (5120 / 6601) := by
    rw [show ((6601 / 5120) : ℝ) = ((5120 / 6601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (4268069 / 12500000) ≤ -Real.log (3639 / 5120) ∧
    -Real.log (3639 / 5120) ≤ (341445521 / 1000000000) := by
  have h := checkLog_sound (w := (1481 / 8759)) (n := 12)
    (lo := (4268069 / 12500000)) (hi := (341445521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3639) = 1/(3639 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-341445521 / 1000000000) (-4268069 / 12500000) (Real.log (3639 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (253612133 / 1000000000) ≤ -Real.log (2560 / 3299) ∧
    -Real.log (2560 / 3299) ≤ (126806067 / 500000000) := by
  have h := checkLog_sound (w := (739 / 5859)) (n := 12)
    (lo := (253612133 / 1000000000)) (hi := (126806067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3299 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3299 / 2560) = 1/(2560 / 3299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (253612133 / 1000000000) (126806067 / 500000000) (Real.log (3299 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3299 / 2560) = -Real.log (2560 / 3299) := by
    rw [show ((3299 / 2560) : ℝ) = ((2560 / 3299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (340621457 / 1000000000) ≤ -Real.log (1821 / 2560) ∧
    -Real.log (1821 / 2560) ≤ (170310729 / 500000000) := by
  have h := checkLog_sound (w := (739 / 4381)) (n := 12)
    (lo := (340621457 / 1000000000)) (hi := (170310729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1821) = 1/(1821 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-170310729 / 500000000) (-340621457 / 1000000000) (Real.log (1821 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (186360057 / 1000000000) ≤ -Real.log (125000 / 150607) ∧
    -Real.log (125000 / 150607) ≤ (93180029 / 500000000) := by
  have h := checkLog_sound (w := (25607 / 275607)) (n := 12)
    (lo := (186360057 / 1000000000)) (hi := (93180029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150607 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150607 / 125000) = 1/(125000 / 150607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (186360057 / 1000000000) (93180029 / 500000000) (Real.log (150607 / 125000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (150607 / 125000) = -Real.log (125000 / 150607) := by
    rw [show ((150607 / 125000) : ℝ) = ((125000 / 150607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (14327003 / 62500000) ≤ -Real.log (99393 / 125000) ∧
    -Real.log (99393 / 125000) ≤ (229232049 / 1000000000) := by
  have h := checkLog_sound (w := (25607 / 224393)) (n := 12)
    (lo := (14327003 / 62500000)) (hi := (229232049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 99393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 99393) = 1/(99393 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-229232049 / 1000000000) (-14327003 / 62500000) (Real.log (99393 / 125000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (93354293 / 500000000) ≤ -Real.log (250000 / 301319) ∧
    -Real.log (250000 / 301319) ≤ (186708587 / 1000000000) := by
  have h := checkLog_sound (w := (51319 / 551319)) (n := 12)
    (lo := (93354293 / 500000000)) (hi := (186708587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301319 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301319 / 250000) = 1/(250000 / 301319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (93354293 / 500000000) (186708587 / 1000000000) (Real.log (301319 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (301319 / 250000) = -Real.log (250000 / 301319) := by
    rw [show ((301319 / 250000) : ℝ) = ((250000 / 301319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (114880197 / 500000000) ≤ -Real.log (198681 / 250000) ∧
    -Real.log (198681 / 250000) ≤ (45952079 / 200000000) := by
  have h := checkLog_sound (w := (51319 / 448681)) (n := 12)
    (lo := (114880197 / 500000000)) (hi := (45952079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 198681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 198681) = 1/(198681 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-45952079 / 200000000) (-114880197 / 500000000) (Real.log (198681 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (68382641 / 500000000) ≤ -Real.log (1000000 / 1146559) ∧
    -Real.log (1000000 / 1146559) ≤ (136765283 / 1000000000) := by
  have h := checkLog_sound (w := (146559 / 2146559)) (n := 12)
    (lo := (68382641 / 500000000)) (hi := (136765283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1146559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1146559 / 1000000) = 1/(1000000 / 1146559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (68382641 / 500000000) (136765283 / 1000000000) (Real.log (1146559 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1146559 / 1000000) = -Real.log (1000000 / 1146559) := by
    rw [show ((1146559 / 1000000) : ℝ) = ((1000000 / 1146559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (79239433 / 500000000) ≤ -Real.log (853441 / 1000000) ∧
    -Real.log (853441 / 1000000) ≤ (158478867 / 1000000000) := by
  have h := checkLog_sound (w := (146559 / 1853441)) (n := 12)
    (lo := (79239433 / 500000000)) (hi := (158478867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 853441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 853441) = 1/(853441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-158478867 / 1000000000) (-79239433 / 500000000) (Real.log (853441 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (34258469 / 250000000) ≤ -Real.log (1000000 / 1146867) ∧
    -Real.log (1000000 / 1146867) ≤ (137033877 / 1000000000) := by
  have h := checkLog_sound (w := (146867 / 2146867)) (n := 12)
    (lo := (34258469 / 250000000)) (hi := (137033877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1146867 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1146867 / 1000000) = 1/(1000000 / 1146867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (34258469 / 250000000) (137033877 / 1000000000) (Real.log (1146867 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1146867 / 1000000) = -Real.log (1000000 / 1146867) := by
    rw [show ((1146867 / 1000000) : ℝ) = ((1000000 / 1146867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (158839823 / 1000000000) ≤ -Real.log (853133 / 1000000) ∧
    -Real.log (853133 / 1000000) ≤ (9927489 / 62500000) := by
  have h := checkLog_sound (w := (146867 / 1853133)) (n := 12)
    (lo := (158839823 / 1000000000)) (hi := (9927489 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 853133) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 853133) = 1/(853133 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-9927489 / 62500000) (-158839823 / 1000000000) (Real.log (853133 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (594233591 / 1000000000) ≤ -Real.log (125000000000 / 226455244371) ∧
    -Real.log (125000000000 / 226455244371) ≤ (74279199 / 125000000) := by
  have h := checkLog_sound (w := (101455244371 / 351455244371)) (n := 12)
    (lo := (594233591 / 1000000000)) (hi := (74279199 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((226455244371 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(226455244371 / 125000000000) = 1/(125000000000 / 226455244371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (594233591 / 1000000000) (74279199 / 125000000) (Real.log (226455244371 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (226455244371 / 125000000000) = -Real.log (125000000000 / 226455244371) := by
    rw [show ((226455244371 / 125000000000) : ℝ) = ((125000000000 / 226455244371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (297756117 / 500000000) ≤ -Real.log (62500000000 / 113372492443) ∧
    -Real.log (62500000000 / 113372492443) ≤ (119102447 / 200000000) := by
  have h := checkLog_sound (w := (50872492443 / 175872492443)) (n := 12)
    (lo := (297756117 / 500000000)) (hi := (119102447 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113372492443 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(113372492443 / 62500000000) = 1/(62500000000 / 113372492443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (297756117 / 500000000) (119102447 / 200000000) (Real.log (113372492443 / 62500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (113372492443 / 62500000000) = -Real.log (62500000000 / 113372492443) := by
    rw [show ((113372492443 / 62500000000) : ℝ) = ((62500000000 / 113372492443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (207796053 / 500000000) ≤ -Real.log (31250000000 / 47352114837) ∧
    -Real.log (31250000000 / 47352114837) ≤ (415592107 / 1000000000) := by
  have h := checkLog_sound (w := (16102114837 / 78602114837)) (n := 12)
    (lo := (207796053 / 500000000)) (hi := (415592107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47352114837 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47352114837 / 31250000000) = 1/(31250000000 / 47352114837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (207796053 / 500000000) (415592107 / 1000000000) (Real.log (47352114837 / 31250000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (47352114837 / 31250000000) = -Real.log (31250000000 / 47352114837) := by
    rw [show ((47352114837 / 31250000000) : ℝ) = ((31250000000 / 47352114837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (20823449 / 50000000) ≤ -Real.log (250000000000 / 379149239233) ∧
    -Real.log (250000000000 / 379149239233) ≤ (416468981 / 1000000000) := by
  have h := checkLog_sound (w := (129149239233 / 629149239233)) (n := 12)
    (lo := (20823449 / 50000000)) (hi := (416468981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((379149239233 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(379149239233 / 250000000000) = 1/(250000000000 / 379149239233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (20823449 / 50000000) (416468981 / 1000000000) (Real.log (379149239233 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (379149239233 / 250000000000) = -Real.log (250000000000 / 379149239233) := by
    rw [show ((379149239233 / 250000000000) : ℝ) = ((250000000000 / 379149239233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (295244149 / 1000000000) ≤ -Real.log (500000000000 / 671727160987) ∧
    -Real.log (500000000000 / 671727160987) ≤ (5904883 / 20000000) := by
  have h := checkLog_sound (w := (171727160987 / 1171727160987)) (n := 12)
    (lo := (295244149 / 1000000000)) (hi := (5904883 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((671727160987 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(671727160987 / 500000000000) = 1/(500000000000 / 671727160987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (295244149 / 1000000000) (5904883 / 20000000) (Real.log (671727160987 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (671727160987 / 500000000000) = -Real.log (500000000000 / 671727160987) := by
    rw [show ((671727160987 / 500000000000) : ℝ) = ((500000000000 / 671727160987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2958737 / 10000000) ≤ -Real.log (50000000000 / 67215018057) ∧
    -Real.log (50000000000 / 67215018057) ≤ (295873701 / 1000000000) := by
  have h := checkLog_sound (w := (17215018057 / 117215018057)) (n := 12)
    (lo := (2958737 / 10000000)) (hi := (295873701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67215018057 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67215018057 / 50000000000) = 1/(50000000000 / 67215018057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2958737 / 10000000) (295873701 / 1000000000) (Real.log (67215018057 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (67215018057 / 50000000000) = -Real.log (50000000000 / 67215018057) := by
    rw [show ((67215018057 / 50000000000) : ℝ) = ((50000000000 / 67215018057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (10902973 / 500000000) ≤ -Real.log (978430084311 / 1000000000000) ∧
    -Real.log (978430084311 / 1000000000000) ≤ (21805947 / 1000000000) := by
  have h := checkLog_sound (w := (21569915689 / 1978430084311)) (n := 12)
    (lo := (10902973 / 500000000)) (hi := (21805947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978430084311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978430084311) = 1/(978430084311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-21805947 / 1000000000) (-10902973 / 500000000) (Real.log (978430084311 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (21713583 / 1000000000) ≤ -Real.log (978520459519 / 1000000000000) ∧
    -Real.log (978520459519 / 1000000000000) ≤ (1357099 / 62500000) := by
  have h := checkLog_sound (w := (21479540481 / 1978520459519)) (n := 12)
    (lo := (21713583 / 1000000000)) (hi := (1357099 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 978520459519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 978520459519) = 1/(978520459519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1357099 / 62500000) (-21713583 / 1000000000) (Real.log (978520459519 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell066
