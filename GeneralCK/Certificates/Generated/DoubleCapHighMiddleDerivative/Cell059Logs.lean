import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell059
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

theorem reflection_log_1_neg : (125440153 / 500000000) ≤ -Real.log (256 / 329) ∧
    -Real.log (256 / 329) ≤ (250880307 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 585)) (n := 12)
    (lo := (125440153 / 500000000)) (hi := (250880307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329 / 256) = 1/(256 / 329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (125440153 / 500000000) (250880307 / 1000000000) (Real.log (329 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (329 / 256) = -Real.log (256 / 329) := by
    rw [show ((329 / 256) : ℝ) = ((256 / 329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (335691291 / 1000000000) ≤ -Real.log (183 / 256) ∧
    -Real.log (183 / 256) ≤ (83922823 / 250000000) := by
  have h := checkLog_sound (w := (73 / 439)) (n := 12)
    (lo := (335691291 / 1000000000)) (hi := (83922823 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 183) = 1/(183 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-83922823 / 250000000) (-335691291 / 1000000000) (Real.log (183 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (10016971 / 40000000) ≤ -Real.log (5120 / 6577) ∧
    -Real.log (5120 / 6577) ≤ (62606069 / 250000000) := by
  have h := checkLog_sound (w := (1457 / 11697)) (n := 12)
    (lo := (10016971 / 40000000)) (hi := (62606069 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6577 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6577 / 5120) = 1/(5120 / 6577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (10016971 / 40000000) (62606069 / 250000000) (Real.log (6577 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6577 / 5120) = -Real.log (5120 / 6577) := by
    rw [show ((6577 / 5120) : ℝ) = ((5120 / 6577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (66974391 / 200000000) ≤ -Real.log (3663 / 5120) ∧
    -Real.log (3663 / 5120) ≤ (83717989 / 250000000) := by
  have h := checkLog_sound (w := (1457 / 8783)) (n := 12)
    (lo := (66974391 / 200000000)) (hi := (83717989 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3663) = 1/(3663 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-83717989 / 250000000) (-66974391 / 200000000) (Real.log (3663 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (91961803 / 500000000) ≤ -Real.log (250000 / 300481) ∧
    -Real.log (250000 / 300481) ≤ (183923607 / 1000000000) := by
  have h := checkLog_sound (w := (50481 / 550481)) (n := 12)
    (lo := (91961803 / 500000000)) (hi := (183923607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300481 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300481 / 250000) = 1/(250000 / 300481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (91961803 / 500000000) (183923607 / 1000000000) (Real.log (300481 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (300481 / 250000) = -Real.log (250000 / 300481) := by
    rw [show ((300481 / 250000) : ℝ) = ((250000 / 300481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (225551447 / 1000000000) ≤ -Real.log (199519 / 250000) ∧
    -Real.log (199519 / 250000) ≤ (28193931 / 125000000) := by
  have h := checkLog_sound (w := (50481 / 449519)) (n := 12)
    (lo := (225551447 / 1000000000)) (hi := (28193931 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 199519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 199519) = 1/(199519 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-28193931 / 125000000) (-225551447 / 1000000000) (Real.log (199519 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23034123 / 125000000) ≤ -Real.log (125000 / 150293) ∧
    -Real.log (125000 / 150293) ≤ (36854597 / 200000000) := by
  have h := checkLog_sound (w := (25293 / 275293)) (n := 12)
    (lo := (23034123 / 125000000)) (hi := (36854597 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((150293 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(150293 / 125000) = 1/(125000 / 150293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (23034123 / 125000000) (36854597 / 200000000) (Real.log (150293 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (150293 / 125000) = -Real.log (125000 / 150293) := by
    rw [show ((150293 / 125000) : ℝ) = ((125000 / 150293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (56519463 / 250000000) ≤ -Real.log (99707 / 125000) ∧
    -Real.log (99707 / 125000) ≤ (226077853 / 1000000000) := by
  have h := checkLog_sound (w := (25293 / 224707)) (n := 12)
    (lo := (56519463 / 250000000)) (hi := (226077853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 99707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 99707) = 1/(99707 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-226077853 / 1000000000) (-56519463 / 250000000) (Real.log (99707 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (134891841 / 1000000000) ≤ -Real.log (1000000 / 1144413) ∧
    -Real.log (1000000 / 1144413) ≤ (67445921 / 500000000) := by
  have h := checkLog_sound (w := (144413 / 2144413)) (n := 12)
    (lo := (134891841 / 1000000000)) (hi := (67445921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1144413 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1144413 / 1000000) = 1/(1000000 / 1144413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (134891841 / 1000000000) (67445921 / 500000000) (Real.log (1144413 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1144413 / 1000000) = -Real.log (1000000 / 1144413) := by
    rw [show ((1144413 / 1000000) : ℝ) = ((1000000 / 1144413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (31193499 / 200000000) ≤ -Real.log (855587 / 1000000) ∧
    -Real.log (855587 / 1000000) ≤ (19495937 / 125000000) := by
  have h := checkLog_sound (w := (144413 / 1855587)) (n := 12)
    (lo := (31193499 / 200000000)) (hi := (19495937 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 855587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 855587) = 1/(855587 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-19495937 / 125000000) (-31193499 / 200000000) (Real.log (855587 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (135160939 / 1000000000) ≤ -Real.log (1000000 / 1144721) ∧
    -Real.log (1000000 / 1144721) ≤ (6758047 / 50000000) := by
  have h := checkLog_sound (w := (144721 / 2144721)) (n := 12)
    (lo := (135160939 / 1000000000)) (hi := (6758047 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1144721 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1144721 / 1000000) = 1/(1000000 / 1144721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (135160939 / 1000000000) (6758047 / 50000000) (Real.log (1144721 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1144721 / 1000000) = -Real.log (1000000 / 1144721) := by
    rw [show ((1144721 / 1000000) : ℝ) = ((1000000 / 1144721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (156327547 / 1000000000) ≤ -Real.log (855279 / 1000000) ∧
    -Real.log (855279 / 1000000) ≤ (39081887 / 250000000) := by
  have h := checkLog_sound (w := (144721 / 1855279)) (n := 12)
    (lo := (156327547 / 1000000000)) (hi := (39081887 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 855279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 855279) = 1/(855279 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-39081887 / 250000000) (-156327547 / 1000000000) (Real.log (855279 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (58529623 / 100000000) ≤ -Real.log (500000000000 / 897761397761) ∧
    -Real.log (500000000000 / 897761397761) ≤ (585296231 / 1000000000) := by
  have h := checkLog_sound (w := (397761397761 / 1397761397761)) (n := 12)
    (lo := (58529623 / 100000000)) (hi := (585296231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((897761397761 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(897761397761 / 500000000000) = 1/(500000000000 / 897761397761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (58529623 / 100000000) (585296231 / 1000000000) (Real.log (897761397761 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (897761397761 / 500000000000) = -Real.log (500000000000 / 897761397761) := by
    rw [show ((897761397761 / 500000000000) : ℝ) = ((500000000000 / 897761397761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (586571597 / 1000000000) ≤ -Real.log (250000000000 / 449453551913) ∧
    -Real.log (250000000000 / 449453551913) ≤ (293285799 / 500000000) := by
  have h := checkLog_sound (w := (199453551913 / 699453551913)) (n := 12)
    (lo := (586571597 / 1000000000)) (hi := (293285799 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((449453551913 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(449453551913 / 250000000000) = 1/(250000000000 / 449453551913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (586571597 / 1000000000) (293285799 / 500000000) (Real.log (449453551913 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (449453551913 / 250000000000) = -Real.log (250000000000 / 449453551913) := by
    rw [show ((449453551913 / 250000000000) : ℝ) = ((250000000000 / 449453551913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (204737527 / 500000000) ≤ -Real.log (500000000000 / 753013497461) ∧
    -Real.log (500000000000 / 753013497461) ≤ (81895011 / 200000000) := by
  have h := checkLog_sound (w := (253013497461 / 1253013497461)) (n := 12)
    (lo := (204737527 / 500000000)) (hi := (81895011 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((753013497461 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(753013497461 / 500000000000) = 1/(500000000000 / 753013497461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (204737527 / 500000000) (81895011 / 200000000) (Real.log (753013497461 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (753013497461 / 500000000000) = -Real.log (500000000000 / 753013497461) := by
    rw [show ((753013497461 / 500000000000) : ℝ) = ((500000000000 / 753013497461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (410350837 / 1000000000) ≤ -Real.log (25000000000 / 37683663133) ∧
    -Real.log (25000000000 / 37683663133) ≤ (205175419 / 500000000) := by
  have h := checkLog_sound (w := (12683663133 / 62683663133)) (n := 12)
    (lo := (410350837 / 1000000000)) (hi := (205175419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37683663133 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37683663133 / 25000000000) = 1/(25000000000 / 37683663133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (410350837 / 1000000000) (205175419 / 500000000) (Real.log (37683663133 / 25000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (37683663133 / 25000000000) = -Real.log (25000000000 / 37683663133) := by
    rw [show ((37683663133 / 25000000000) : ℝ) = ((25000000000 / 37683663133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (290859337 / 1000000000) ≤ -Real.log (500000000000 / 668788212069) ∧
    -Real.log (500000000000 / 668788212069) ≤ (145429669 / 500000000) := by
  have h := checkLog_sound (w := (168788212069 / 1168788212069)) (n := 12)
    (lo := (290859337 / 1000000000)) (hi := (145429669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((668788212069 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(668788212069 / 500000000000) = 1/(500000000000 / 668788212069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (290859337 / 1000000000) (145429669 / 500000000) (Real.log (668788212069 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (668788212069 / 500000000000) = -Real.log (500000000000 / 668788212069) := by
    rw [show ((668788212069 / 500000000000) : ℝ) = ((500000000000 / 668788212069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (145744243 / 500000000) ≤ -Real.log (500000000000 / 669209111881) ∧
    -Real.log (500000000000 / 669209111881) ≤ (291488487 / 1000000000) := by
  have h := checkLog_sound (w := (169209111881 / 1169209111881)) (n := 12)
    (lo := (145744243 / 500000000)) (hi := (291488487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((669209111881 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(669209111881 / 500000000000) = 1/(500000000000 / 669209111881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (145744243 / 500000000) (291488487 / 1000000000) (Real.log (669209111881 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (669209111881 / 500000000000) = -Real.log (500000000000 / 669209111881) := by
    rw [show ((669209111881 / 500000000000) : ℝ) = ((500000000000 / 669209111881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1322913 / 62500000) ≤ -Real.log (979055832159 / 1000000000000) ∧
    -Real.log (979055832159 / 1000000000000) ≤ (21166609 / 1000000000) := by
  have h := checkLog_sound (w := (20944167841 / 1979055832159)) (n := 12)
    (lo := (1322913 / 62500000)) (hi := (21166609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979055832159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979055832159) = 1/(979055832159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-21166609 / 1000000000) (-1322913 / 62500000) (Real.log (979055832159 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (10537827 / 500000000) ≤ -Real.log (979144885431 / 1000000000000) ∧
    -Real.log (979144885431 / 1000000000000) ≤ (4215131 / 200000000) := by
  have h := checkLog_sound (w := (20855114569 / 1979144885431)) (n := 12)
    (lo := (10537827 / 500000000)) (hi := (4215131 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979144885431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979144885431) = 1/(979144885431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4215131 / 200000000) (-10537827 / 500000000) (Real.log (979144885431 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell059
