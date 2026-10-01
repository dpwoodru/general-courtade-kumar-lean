import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0081
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

theorem reflection_log_1_neg : (349225389 / 1000000000) ≤ -Real.log (256 / 363) ∧
    -Real.log (256 / 363) ≤ (34922539 / 100000000) := by
  have h := checkLog_sound (w := (107 / 619)) (n := 12)
    (lo := (349225389 / 1000000000)) (hi := (34922539 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363 / 256) = 1/(256 / 363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (349225389 / 1000000000) (34922539 / 100000000) (Real.log (363 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (363 / 256) = -Real.log (256 / 363) := by
    rw [show ((363 / 256) : ℝ) = ((256 / 363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (270615569 / 500000000) ≤ -Real.log (149 / 256) ∧
    -Real.log (149 / 256) ≤ (541231139 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 405)) (n := 12)
    (lo := (270615569 / 500000000)) (hi := (541231139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 149) = 1/(149 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-541231139 / 1000000000) (-270615569 / 500000000) (Real.log (149 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (348398601 / 1000000000) ≤ -Real.log (2560 / 3627) ∧
    -Real.log (2560 / 3627) ≤ (174199301 / 500000000) := by
  have h := checkLog_sound (w := (1067 / 6187)) (n := 12)
    (lo := (348398601 / 1000000000)) (hi := (174199301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3627 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3627 / 2560) = 1/(2560 / 3627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (348398601 / 1000000000) (174199301 / 500000000) (Real.log (3627 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3627 / 2560) = -Real.log (2560 / 3627) := by
    rw [show ((3627 / 2560) : ℝ) = ((2560 / 3627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (539219739 / 1000000000) ≤ -Real.log (1493 / 2560) ∧
    -Real.log (1493 / 2560) ≤ (26960987 / 50000000) := by
  have h := checkLog_sound (w := (1067 / 4053)) (n := 12)
    (lo := (539219739 / 1000000000)) (hi := (26960987 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1493) = 1/(1493 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-26960987 / 50000000) (-539219739 / 1000000000) (Real.log (1493 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (2430221 / 4000000) ≤ -Real.log (128 / 235) ∧
    -Real.log (128 / 235) ≤ (607555251 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 363)) (n := 12)
    (lo := (2430221 / 4000000)) (hi := (607555251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((235 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(235 / 128) = 1/(128 / 235) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (2430221 / 4000000) (607555251 / 1000000000) (Real.log (235 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (235 / 128) = -Real.log (128 / 235) := by
    rw [show ((235 / 128) : ℝ) = ((128 / 235) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (72300313 / 40000000) ≤ -Real.log (21 / 128) ∧
    -Real.log (21 / 128) ≤ (451876957 / 250000000) := by
  have h := checkLog_sound (w := (11 / 53)) (n := 12)
    (lo := (84242693 / 200000000)) (hi := (210606733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 21) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(32 / 21) = 1/(21 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-451876957 / 250000000) (-72300313 / 40000000) (Real.log (21 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (303138919 / 500000000) ≤ -Real.log (1280 / 2347) ∧
    -Real.log (1280 / 2347) ≤ (606277839 / 1000000000) := by
  have h := checkLog_sound (w := (1067 / 3627)) (n := 12)
    (lo := (303138919 / 500000000)) (hi := (606277839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2347 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2347 / 1280) = 1/(1280 / 2347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (303138919 / 500000000) (606277839 / 1000000000) (Real.log (2347 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2347 / 1280) = -Real.log (1280 / 2347) := by
    rw [show ((2347 / 1280) : ℝ) = ((1280 / 2347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (179332319 / 100000000) ≤ -Real.log (213 / 1280) ∧
    -Real.log (213 / 1280) ≤ (1793323193 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 533)) (n := 12)
    (lo := (40702883 / 100000000)) (hi := (407028831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 213) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 213) = 1/(213 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1793323193 / 1000000000) (-179332319 / 100000000) (Real.log (213 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (95865629 / 200000000) ≤ -Real.log (1000000 / 1614989) ∧
    -Real.log (1000000 / 1614989) ≤ (239664073 / 500000000) := by
  have h := checkLog_sound (w := (614989 / 2614989)) (n := 12)
    (lo := (95865629 / 200000000)) (hi := (239664073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1614989 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1614989 / 1000000) = 1/(1000000 / 1614989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (95865629 / 200000000) (239664073 / 500000000) (Real.log (1614989 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1614989 / 1000000) = -Real.log (1000000 / 1614989) := by
    rw [show ((1614989 / 1000000) : ℝ) = ((1000000 / 1614989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (954483373 / 1000000000) ≤ -Real.log (385011 / 1000000) ∧
    -Real.log (385011 / 1000000) ≤ (7635867 / 8000000) := by
  have h := checkLog_sound (w := (114989 / 885011)) (n := 12)
    (lo := (261336193 / 1000000000)) (hi := (130668097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 385011) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 385011) = 1/(385011 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-7635867 / 8000000) (-954483373 / 1000000000) (Real.log (385011 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (240271757 / 500000000) ≤ -Real.log (1000000 / 1616953) ∧
    -Real.log (1000000 / 1616953) ≤ (96108703 / 200000000) := by
  have h := checkLog_sound (w := (616953 / 2616953)) (n := 12)
    (lo := (240271757 / 500000000)) (hi := (96108703 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1616953 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1616953 / 1000000) = 1/(1000000 / 1616953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (240271757 / 500000000) (96108703 / 200000000) (Real.log (1616953 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1616953 / 1000000) = -Real.log (1000000 / 1616953) := by
    rw [show ((1616953 / 1000000) : ℝ) = ((1000000 / 1616953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (959597581 / 1000000000) ≤ -Real.log (383047 / 1000000) ∧
    -Real.log (383047 / 1000000) ≤ (959597583 / 1000000000) := by
  have h := checkLog_sound (w := (116953 / 883047)) (n := 12)
    (lo := (266450401 / 1000000000)) (hi := (133225201 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 383047) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 383047) = 1/(383047 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-959597583 / 1000000000) (-959597581 / 1000000000) (Real.log (383047 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (197793237 / 500000000) ≤ -Real.log (200000 / 297051) ∧
    -Real.log (200000 / 297051) ≤ (15823459 / 40000000) := by
  have h := checkLog_sound (w := (97051 / 497051)) (n := 12)
    (lo := (197793237 / 500000000)) (hi := (15823459 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297051 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297051 / 200000) = 1/(200000 / 297051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (197793237 / 500000000) (15823459 / 40000000) (Real.log (297051 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (297051 / 200000) = -Real.log (200000 / 297051) := by
    rw [show ((297051 / 200000) : ℝ) = ((200000 / 297051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (332041823 / 500000000) ≤ -Real.log (102949 / 200000) ∧
    -Real.log (102949 / 200000) ≤ (664083647 / 1000000000) := by
  have h := checkLog_sound (w := (97051 / 302949)) (n := 12)
    (lo := (332041823 / 500000000)) (hi := (664083647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 102949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 102949) = 1/(102949 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-664083647 / 1000000000) (-332041823 / 500000000) (Real.log (102949 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (19843413 / 50000000) ≤ -Real.log (25000 / 37179) ∧
    -Real.log (25000 / 37179) ≤ (396868261 / 1000000000) := by
  have h := checkLog_sound (w := (12179 / 62179)) (n := 12)
    (lo := (19843413 / 50000000)) (hi := (396868261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37179 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37179 / 25000) = 1/(25000 / 37179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (19843413 / 50000000) (396868261 / 1000000000) (Real.log (37179 / 25000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (37179 / 25000) = -Real.log (25000 / 37179) := by
    rw [show ((37179 / 25000) : ℝ) = ((25000 / 37179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (667791373 / 1000000000) ≤ -Real.log (12821 / 25000) ∧
    -Real.log (12821 / 25000) ≤ (333895687 / 500000000) := by
  have h := checkLog_sound (w := (12179 / 37821)) (n := 12)
    (lo := (667791373 / 1000000000)) (hi := (333895687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 12821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 12821) = 1/(12821 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-333895687 / 500000000) (-667791373 / 1000000000) (Real.log (12821 / 25000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (716905759 / 500000000) ≤ -Real.log (25000000000 / 104866419401) ∧
    -Real.log (25000000000 / 104866419401) ≤ (1433811521 / 1000000000) := by
  have h := checkLog_sound (w := (4866419401 / 204866419401)) (n := 12)
    (lo := (23758579 / 500000000)) (hi := (47517159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((104866419401 / 100000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(104866419401 / 100000000000) = 1/(25000000000 / 104866419401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (716905759 / 500000000) (1433811521 / 1000000000) (Real.log (104866419401 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (104866419401 / 25000000000) = -Real.log (25000000000 / 104866419401) := by
    rw [show ((104866419401 / 25000000000) : ℝ) = ((25000000000 / 104866419401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (720070547 / 500000000) ≤ -Real.log (500000000000 / 2110645690999) ∧
    -Real.log (500000000000 / 2110645690999) ≤ (1440141097 / 1000000000) := by
  have h := checkLog_sound (w := (110645690999 / 4110645690999)) (n := 12)
    (lo := (26923367 / 500000000)) (hi := (10769347 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2110645690999 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2110645690999 / 2000000000000) = 1/(500000000000 / 2110645690999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (720070547 / 500000000) (1440141097 / 1000000000) (Real.log (2110645690999 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2110645690999 / 500000000000) = -Real.log (500000000000 / 2110645690999) := by
    rw [show ((2110645690999 / 500000000000) : ℝ) = ((500000000000 / 2110645690999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (26491753 / 25000000) ≤ -Real.log (100000000000 / 288541899387) ∧
    -Real.log (100000000000 / 288541899387) ≤ (529835061 / 500000000) := by
  have h := checkLog_sound (w := (88541899387 / 488541899387)) (n := 12)
    (lo := (18326147 / 50000000)) (hi := (366522941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((288541899387 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(288541899387 / 200000000000) = 1/(100000000000 / 288541899387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (26491753 / 25000000) (529835061 / 500000000) (Real.log (288541899387 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (288541899387 / 100000000000) = -Real.log (100000000000 / 288541899387) := by
    rw [show ((288541899387 / 100000000000) : ℝ) = ((100000000000 / 288541899387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1064659633 / 1000000000) ≤ -Real.log (15625000000 / 45310184463) ∧
    -Real.log (15625000000 / 45310184463) ≤ (212931927 / 200000000) := by
  have h := checkLog_sound (w := (14060184463 / 76560184463)) (n := 12)
    (lo := (371512453 / 1000000000)) (hi := (185756227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45310184463 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(45310184463 / 31250000000) = 1/(15625000000 / 45310184463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1064659633 / 1000000000) (212931927 / 200000000) (Real.log (45310184463 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (45310184463 / 15625000000) = -Real.log (15625000000 / 45310184463) := by
    rw [show ((45310184463 / 15625000000) : ℝ) = ((15625000000 / 45310184463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0081
