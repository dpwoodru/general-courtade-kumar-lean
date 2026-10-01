import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_4224_neg : (91075987 / 500000000) ≤ -Real.log (125000000000 / 149974564853) ∧
    -Real.log (125000000000 / 149974564853) ≤ (7286079 / 40000000) := by
  have h := checkLog_sound (w := (24974564853 / 274974564853)) (n := 12)
    (lo := (91075987 / 500000000)) (hi := (7286079 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149974564853 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149974564853 / 125000000000) = 1/(125000000000 / 149974564853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4224 : Bounds (91075987 / 500000000) (7286079 / 40000000) (Real.log (149974564853 / 125000000000)) := by
  have h := reflection_log_4224_neg
  have he : Real.log (149974564853 / 125000000000) = -Real.log (125000000000 / 149974564853) := by
    rw [show ((149974564853 / 125000000000) : ℝ) = ((125000000000 / 149974564853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4225_neg : (182292751 / 500000000) ≤ -Real.log (50000000000 / 71995852141) ∧
    -Real.log (50000000000 / 71995852141) ≤ (364585503 / 1000000000) := by
  have h := checkLog_sound (w := (21995852141 / 121995852141)) (n := 12)
    (lo := (182292751 / 500000000)) (hi := (364585503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71995852141 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71995852141 / 50000000000) = 1/(50000000000 / 71995852141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4225 : Bounds (182292751 / 500000000) (364585503 / 1000000000) (Real.log (71995852141 / 50000000000)) := by
  have h := reflection_log_4225_neg
  have he : Real.log (71995852141 / 50000000000) = -Real.log (50000000000 / 71995852141) := by
    rw [show ((71995852141 / 50000000000) : ℝ) = ((50000000000 / 71995852141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4226_neg : (182396113 / 500000000) ≤ -Real.log (500000000000 / 720107369449) ∧
    -Real.log (500000000000 / 720107369449) ≤ (364792227 / 1000000000) := by
  have h := checkLog_sound (w := (220107369449 / 1220107369449)) (n := 12)
    (lo := (182396113 / 500000000)) (hi := (364792227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((720107369449 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(720107369449 / 500000000000) = 1/(500000000000 / 720107369449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4226 : Bounds (182396113 / 500000000) (364792227 / 1000000000) (Real.log (720107369449 / 500000000000)) := by
  have h := reflection_log_4226_neg
  have he : Real.log (720107369449 / 500000000000) = -Real.log (500000000000 / 720107369449) := by
    rw [show ((720107369449 / 500000000000) : ℝ) = ((500000000000 / 720107369449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4227_neg : (165938077 / 1000000000) ≤ -Real.log (2000 / 2361) ∧
    -Real.log (2000 / 2361) ≤ (82969039 / 500000000) := by
  have h := checkLog_sound (w := (361 / 4361)) (n := 12)
    (lo := (165938077 / 1000000000)) (hi := (82969039 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2361 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2361 / 2000) = 1/(2000 / 2361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4227 : Bounds (165938077 / 1000000000) (82969039 / 500000000) (Real.log (2361 / 2000)) := by
  have h := reflection_log_4227_neg
  have he : Real.log (2361 / 2000) = -Real.log (2000 / 2361) := by
    rw [show ((2361 / 2000) : ℝ) = ((2000 / 2361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4228_neg : (2488261 / 12500000) ≤ -Real.log (1639 / 2000) ∧
    -Real.log (1639 / 2000) ≤ (199060881 / 1000000000) := by
  have h := checkLog_sound (w := (361 / 3639)) (n := 12)
    (lo := (2488261 / 12500000)) (hi := (199060881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1639) = 1/(1639 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4228 : Bounds (-199060881 / 1000000000) (-2488261 / 12500000) (Real.log (1639 / 2000)) := by
  have h := reflection_log_4228_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4229_neg : (180483 / 1000000000) ≤ -Real.log (2000000 / 2000361) ∧
    -Real.log (2000000 / 2000361) ≤ (45121 / 250000000) := by
  have h := checkLog_sound (w := (361 / 4000361)) (n := 12)
    (lo := (180483 / 1000000000)) (hi := (45121 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000361 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000361 / 2000000) = 1/(2000000 / 2000361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4229 : Bounds (180483 / 1000000000) (45121 / 250000000) (Real.log (2000361 / 2000000)) := by
  have h := reflection_log_4229_neg
  have he : Real.log (2000361 / 2000000) = -Real.log (2000000 / 2000361) := by
    rw [show ((2000361 / 2000000) : ℝ) = ((2000000 / 2000361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4230_neg : (45129 / 250000000) ≤ -Real.log (1999639 / 2000000) ∧
    -Real.log (1999639 / 2000000) ≤ (180517 / 1000000000) := by
  have h := checkLog_sound (w := (361 / 3999639)) (n := 12)
    (lo := (45129 / 250000000)) (hi := (180517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999639) = 1/(1999639 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4230 : Bounds (-180517 / 1000000000) (-45129 / 250000000) (Real.log (1999639 / 2000000)) := by
  have h := reflection_log_4230_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4231_neg : (86768347 / 1000000000) ≤ -Real.log (250000 / 272661) ∧
    -Real.log (250000 / 272661) ≤ (21692087 / 250000000) := by
  have h := checkLog_sound (w := (22661 / 522661)) (n := 12)
    (lo := (86768347 / 1000000000)) (hi := (21692087 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272661 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272661 / 250000) = 1/(250000 / 272661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4231 : Bounds (86768347 / 1000000000) (21692087 / 250000000) (Real.log (272661 / 250000)) := by
  have h := reflection_log_4231_neg
  have he : Real.log (272661 / 250000) = -Real.log (250000 / 272661) := by
    rw [show ((272661 / 250000) : ℝ) = ((250000 / 272661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4232_neg : (47509311 / 500000000) ≤ -Real.log (227339 / 250000) ∧
    -Real.log (227339 / 250000) ≤ (95018623 / 1000000000) := by
  have h := checkLog_sound (w := (22661 / 477339)) (n := 12)
    (lo := (47509311 / 500000000)) (hi := (95018623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227339) = 1/(227339 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4232 : Bounds (-95018623 / 1000000000) (-47509311 / 500000000) (Real.log (227339 / 250000)) := by
  have h := reflection_log_4232_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4233_neg : (86981043 / 1000000000) ≤ -Real.log (250000 / 272719) ∧
    -Real.log (250000 / 272719) ≤ (21745261 / 250000000) := by
  have h := checkLog_sound (w := (22719 / 522719)) (n := 12)
    (lo := (86981043 / 1000000000)) (hi := (21745261 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272719 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272719 / 250000) = 1/(250000 / 272719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4233 : Bounds (86981043 / 1000000000) (21745261 / 250000000) (Real.log (272719 / 250000)) := by
  have h := reflection_log_4233_neg
  have he : Real.log (272719 / 250000) = -Real.log (250000 / 272719) := by
    rw [show ((272719 / 250000) : ℝ) = ((250000 / 272719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4234_neg : (4763689 / 50000000) ≤ -Real.log (227281 / 250000) ∧
    -Real.log (227281 / 250000) ≤ (95273781 / 1000000000) := by
  have h := checkLog_sound (w := (22719 / 477281)) (n := 12)
    (lo := (4763689 / 50000000)) (hi := (95273781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227281) = 1/(227281 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4234 : Bounds (-95273781 / 1000000000) (-4763689 / 50000000) (Real.log (227281 / 250000)) := by
  have h := reflection_log_4234_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4235_neg : (8292737 / 1000000000) ≤ -Real.log (61983847039 / 62500000000) ∧
    -Real.log (61983847039 / 62500000000) ≤ (4146369 / 500000000) := by
  have h := checkLog_sound (w := (516152961 / 124483847039)) (n := 12)
    (lo := (8292737 / 1000000000)) (hi := (4146369 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61983847039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61983847039) = 1/(61983847039 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4235 : Bounds (-4146369 / 500000000) (-8292737 / 1000000000) (Real.log (61983847039 / 62500000000)) := by
  have h := reflection_log_4235_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4236_neg : (4125137 / 500000000) ≤ -Real.log (61986479079 / 62500000000) ∧
    -Real.log (61986479079 / 62500000000) ≤ (330011 / 40000000) := by
  have h := checkLog_sound (w := (513520921 / 124486479079)) (n := 12)
    (lo := (4125137 / 500000000)) (hi := (330011 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61986479079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61986479079) = 1/(61986479079 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4236 : Bounds (-330011 / 40000000) (-4125137 / 500000000) (Real.log (61986479079 / 62500000000)) := by
  have h := reflection_log_4236_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4237_neg : (181786969 / 1000000000) ≤ -Real.log (250000000000 / 299839666753) ∧
    -Real.log (250000000000 / 299839666753) ≤ (18178697 / 100000000) := by
  have h := checkLog_sound (w := (49839666753 / 549839666753)) (n := 12)
    (lo := (181786969 / 1000000000)) (hi := (18178697 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299839666753 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299839666753 / 250000000000) = 1/(250000000000 / 299839666753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4237 : Bounds (181786969 / 1000000000) (18178697 / 100000000) (Real.log (299839666753 / 250000000000)) := by
  have h := reflection_log_4237_neg
  have he : Real.log (299839666753 / 250000000000) = -Real.log (250000000000 / 299839666753) := by
    rw [show ((299839666753 / 250000000000) : ℝ) = ((250000000000 / 299839666753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4238_neg : (182254823 / 1000000000) ≤ -Real.log (250000000000 / 299979980729) ∧
    -Real.log (250000000000 / 299979980729) ≤ (22781853 / 125000000) := by
  have h := checkLog_sound (w := (49979980729 / 549979980729)) (n := 12)
    (lo := (182254823 / 1000000000)) (hi := (22781853 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299979980729 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299979980729 / 250000000000) = 1/(250000000000 / 299979980729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4238 : Bounds (182254823 / 1000000000) (22781853 / 125000000) (Real.log (299979980729 / 250000000000)) := by
  have h := reflection_log_4238_neg
  have he : Real.log (299979980729 / 250000000000) = -Real.log (250000000000 / 299979980729) := by
    rw [show ((299979980729 / 250000000000) : ℝ) = ((250000000000 / 299979980729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4239_neg : (182396113 / 500000000) ≤ -Real.log (62500000000 / 90013421181) ∧
    -Real.log (62500000000 / 90013421181) ≤ (364792227 / 1000000000) := by
  have h := checkLog_sound (w := (27513421181 / 152513421181)) (n := 12)
    (lo := (182396113 / 500000000)) (hi := (364792227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90013421181 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90013421181 / 62500000000) = 1/(62500000000 / 90013421181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4239 : Bounds (182396113 / 500000000) (364792227 / 1000000000) (Real.log (90013421181 / 62500000000)) := by
  have h := reflection_log_4239_neg
  have he : Real.log (90013421181 / 62500000000) = -Real.log (62500000000 / 90013421181) := by
    rw [show ((90013421181 / 62500000000) : ℝ) = ((62500000000 / 90013421181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4240_neg : (182499479 / 500000000) ≤ -Real.log (250000000000 / 360128126907) ∧
    -Real.log (250000000000 / 360128126907) ≤ (364998959 / 1000000000) := by
  have h := checkLog_sound (w := (110128126907 / 610128126907)) (n := 12)
    (lo := (182499479 / 500000000)) (hi := (364998959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((360128126907 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(360128126907 / 250000000000) = 1/(250000000000 / 360128126907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4240 : Bounds (182499479 / 500000000) (364998959 / 1000000000) (Real.log (360128126907 / 250000000000)) := by
  have h := reflection_log_4240_neg
  have he : Real.log (360128126907 / 250000000000) = -Real.log (250000000000 / 360128126907) := by
    rw [show ((360128126907 / 250000000000) : ℝ) = ((250000000000 / 360128126907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4241_neg : (166022783 / 1000000000) ≤ -Real.log (5000 / 5903) ∧
    -Real.log (5000 / 5903) ≤ (1297053 / 7812500) := by
  have h := checkLog_sound (w := (903 / 10903)) (n := 12)
    (lo := (166022783 / 1000000000)) (hi := (1297053 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5903 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5903 / 5000) = 1/(5000 / 5903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4241 : Bounds (166022783 / 1000000000) (1297053 / 7812500) (Real.log (5903 / 5000)) := by
  have h := reflection_log_4241_neg
  have he : Real.log (5903 / 5000) = -Real.log (5000 / 5903) := by
    rw [show ((5903 / 5000) : ℝ) = ((5000 / 5903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4242_neg : (199182913 / 1000000000) ≤ -Real.log (4097 / 5000) ∧
    -Real.log (4097 / 5000) ≤ (99591457 / 500000000) := by
  have h := checkLog_sound (w := (903 / 9097)) (n := 12)
    (lo := (199182913 / 1000000000)) (hi := (99591457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4097) = 1/(4097 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4242 : Bounds (-99591457 / 500000000) (-199182913 / 1000000000) (Real.log (4097 / 5000)) := by
  have h := reflection_log_4242_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4243_neg : (180583 / 1000000000) ≤ -Real.log (5000000 / 5000903) ∧
    -Real.log (5000000 / 5000903) ≤ (22573 / 125000000) := by
  have h := checkLog_sound (w := (903 / 10000903)) (n := 12)
    (lo := (180583 / 1000000000)) (hi := (22573 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000903 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000903 / 5000000) = 1/(5000000 / 5000903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4243 : Bounds (180583 / 1000000000) (22573 / 125000000) (Real.log (5000903 / 5000000)) := by
  have h := reflection_log_4243_neg
  have he : Real.log (5000903 / 5000000) = -Real.log (5000000 / 5000903) := by
    rw [show ((5000903 / 5000000) : ℝ) = ((5000000 / 5000903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4244_neg : (22577 / 125000000) ≤ -Real.log (4999097 / 5000000) ∧
    -Real.log (4999097 / 5000000) ≤ (180617 / 1000000000) := by
  have h := checkLog_sound (w := (903 / 9999097)) (n := 12)
    (lo := (22577 / 125000000)) (hi := (180617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999097) = 1/(4999097 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4244 : Bounds (-180617 / 1000000000) (-22577 / 125000000) (Real.log (4999097 / 5000000)) := by
  have h := reflection_log_4244_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4245_neg : (86815107 / 1000000000) ≤ -Real.log (200000 / 218139) ∧
    -Real.log (200000 / 218139) ≤ (21703777 / 250000000) := by
  have h := checkLog_sound (w := (18139 / 418139)) (n := 12)
    (lo := (86815107 / 1000000000)) (hi := (21703777 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218139 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218139 / 200000) = 1/(200000 / 218139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4245 : Bounds (86815107 / 1000000000) (21703777 / 250000000) (Real.log (218139 / 200000)) := by
  have h := reflection_log_4245_neg
  have he : Real.log (218139 / 200000) = -Real.log (200000 / 218139) := by
    rw [show ((218139 / 200000) : ℝ) = ((200000 / 218139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4246_neg : (95074707 / 1000000000) ≤ -Real.log (181861 / 200000) ∧
    -Real.log (181861 / 200000) ≤ (23768677 / 250000000) := by
  have h := checkLog_sound (w := (18139 / 381861)) (n := 12)
    (lo := (95074707 / 1000000000)) (hi := (23768677 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 181861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 181861) = 1/(181861 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4246 : Bounds (-23768677 / 250000000) (-95074707 / 1000000000) (Real.log (181861 / 200000)) := by
  have h := reflection_log_4246_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4247_neg : (87027793 / 1000000000) ≤ -Real.log (1000000 / 1090927) ∧
    -Real.log (1000000 / 1090927) ≤ (43513897 / 500000000) := by
  have h := checkLog_sound (w := (90927 / 2090927)) (n := 12)
    (lo := (87027793 / 1000000000)) (hi := (43513897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090927 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090927 / 1000000) = 1/(1000000 / 1090927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4247 : Bounds (87027793 / 1000000000) (43513897 / 500000000) (Real.log (1090927 / 1000000)) := by
  have h := reflection_log_4247_neg
  have he : Real.log (1090927 / 1000000) = -Real.log (1000000 / 1090927) := by
    rw [show ((1090927 / 1000000) : ℝ) = ((1000000 / 1090927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4248_neg : (95329879 / 1000000000) ≤ -Real.log (909073 / 1000000) ∧
    -Real.log (909073 / 1000000) ≤ (2383247 / 25000000) := by
  have h := checkLog_sound (w := (90927 / 1909073)) (n := 12)
    (lo := (95329879 / 1000000000)) (hi := (2383247 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909073) = 1/(909073 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4248 : Bounds (-2383247 / 25000000) (-95329879 / 1000000000) (Real.log (909073 / 1000000)) := by
  have h := reflection_log_4248_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4249_neg : (4151043 / 500000000) ≤ -Real.log (991732280671 / 1000000000000) ∧
    -Real.log (991732280671 / 1000000000000) ≤ (8302087 / 1000000000) := by
  have h := checkLog_sound (w := (8267719329 / 1991732280671)) (n := 12)
    (lo := (4151043 / 500000000)) (hi := (8302087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991732280671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991732280671) = 1/(991732280671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4249 : Bounds (-8302087 / 1000000000) (-4151043 / 500000000) (Real.log (991732280671 / 1000000000000)) := by
  have h := reflection_log_4249_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4250_neg : (8259599 / 1000000000) ≤ -Real.log (39670976679 / 40000000000) ∧
    -Real.log (39670976679 / 40000000000) ≤ (20649 / 2500000) := by
  have h := checkLog_sound (w := (329023321 / 79670976679)) (n := 12)
    (lo := (8259599 / 1000000000)) (hi := (20649 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39670976679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39670976679) = 1/(39670976679 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4250 : Bounds (-20649 / 2500000) (-8259599 / 1000000000) (Real.log (39670976679 / 40000000000)) := by
  have h := reflection_log_4250_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4251_neg : (36377963 / 200000000) ≤ -Real.log (500000000000 / 599741010991) ∧
    -Real.log (500000000000 / 599741010991) ≤ (22736227 / 125000000) := by
  have h := checkLog_sound (w := (99741010991 / 1099741010991)) (n := 12)
    (lo := (36377963 / 200000000)) (hi := (22736227 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599741010991 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599741010991 / 500000000000) = 1/(500000000000 / 599741010991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4251 : Bounds (36377963 / 200000000) (22736227 / 125000000) (Real.log (599741010991 / 500000000000)) := by
  have h := reflection_log_4251_neg
  have he : Real.log (599741010991 / 500000000000) = -Real.log (500000000000 / 599741010991) := by
    rw [show ((599741010991 / 500000000000) : ℝ) = ((500000000000 / 599741010991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4252_neg : (182357673 / 1000000000) ≤ -Real.log (500000000000 / 600021670427) ∧
    -Real.log (500000000000 / 600021670427) ≤ (91178837 / 500000000) := by
  have h := checkLog_sound (w := (100021670427 / 1100021670427)) (n := 12)
    (lo := (182357673 / 1000000000)) (hi := (91178837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600021670427 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600021670427 / 500000000000) = 1/(500000000000 / 600021670427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4252 : Bounds (182357673 / 1000000000) (91178837 / 500000000) (Real.log (600021670427 / 500000000000)) := by
  have h := reflection_log_4252_neg
  have he : Real.log (600021670427 / 500000000000) = -Real.log (500000000000 / 600021670427) := by
    rw [show ((600021670427 / 500000000000) : ℝ) = ((500000000000 / 600021670427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4253_neg : (182499479 / 500000000) ≤ -Real.log (500000000000 / 720256253813) ∧
    -Real.log (500000000000 / 720256253813) ≤ (364998959 / 1000000000) := by
  have h := checkLog_sound (w := (220256253813 / 1220256253813)) (n := 12)
    (lo := (182499479 / 500000000)) (hi := (364998959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((720256253813 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(720256253813 / 500000000000) = 1/(500000000000 / 720256253813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4253 : Bounds (182499479 / 500000000) (364998959 / 1000000000) (Real.log (720256253813 / 500000000000)) := by
  have h := reflection_log_4253_neg
  have he : Real.log (720256253813 / 500000000000) = -Real.log (500000000000 / 720256253813) := by
    rw [show ((720256253813 / 500000000000) : ℝ) = ((500000000000 / 720256253813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4254_neg : (365205697 / 1000000000) ≤ -Real.log (250000000000 / 360202587259) ∧
    -Real.log (250000000000 / 360202587259) ≤ (182602849 / 500000000) := by
  have h := checkLog_sound (w := (110202587259 / 610202587259)) (n := 12)
    (lo := (365205697 / 1000000000)) (hi := (182602849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((360202587259 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(360202587259 / 250000000000) = 1/(250000000000 / 360202587259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4254 : Bounds (365205697 / 1000000000) (182602849 / 500000000) (Real.log (360202587259 / 250000000000)) := by
  have h := reflection_log_4254_neg
  have he : Real.log (360202587259 / 250000000000) = -Real.log (250000000000 / 360202587259) := by
    rw [show ((360202587259 / 250000000000) : ℝ) = ((250000000000 / 360202587259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4255_neg : (83053741 / 500000000) ≤ -Real.log (10000 / 11807) ∧
    -Real.log (10000 / 11807) ≤ (166107483 / 1000000000) := by
  have h := checkLog_sound (w := (1807 / 21807)) (n := 12)
    (lo := (83053741 / 500000000)) (hi := (166107483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11807 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11807 / 10000) = 1/(10000 / 11807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4255 : Bounds (83053741 / 500000000) (166107483 / 1000000000) (Real.log (11807 / 10000)) := by
  have h := reflection_log_4255_neg
  have he : Real.log (11807 / 10000) = -Real.log (10000 / 11807) := by
    rw [show ((11807 / 10000) : ℝ) = ((10000 / 11807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4256_neg : (199304961 / 1000000000) ≤ -Real.log (8193 / 10000) ∧
    -Real.log (8193 / 10000) ≤ (99652481 / 500000000) := by
  have h := checkLog_sound (w := (1807 / 18193)) (n := 12)
    (lo := (199304961 / 1000000000)) (hi := (99652481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8193) = 1/(8193 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4256 : Bounds (-99652481 / 500000000) (-199304961 / 1000000000) (Real.log (8193 / 10000)) := by
  have h := reflection_log_4256_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4257_neg : (180683 / 1000000000) ≤ -Real.log (10000000 / 10001807) ∧
    -Real.log (10000000 / 10001807) ≤ (45171 / 250000000) := by
  have h := checkLog_sound (w := (1807 / 20001807)) (n := 12)
    (lo := (180683 / 1000000000)) (hi := (45171 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001807 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001807 / 10000000) = 1/(10000000 / 10001807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4257 : Bounds (180683 / 1000000000) (45171 / 250000000) (Real.log (10001807 / 10000000)) := by
  have h := reflection_log_4257_neg
  have he : Real.log (10001807 / 10000000) = -Real.log (10000000 / 10001807) := by
    rw [show ((10001807 / 10000000) : ℝ) = ((10000000 / 10001807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4258_neg : (45179 / 250000000) ≤ -Real.log (9998193 / 10000000) ∧
    -Real.log (9998193 / 10000000) ≤ (180717 / 1000000000) := by
  have h := checkLog_sound (w := (1807 / 19998193)) (n := 12)
    (lo := (45179 / 250000000)) (hi := (180717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998193) = 1/(9998193 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4258 : Bounds (-180717 / 1000000000) (-45179 / 250000000) (Real.log (9998193 / 10000000)) := by
  have h := reflection_log_4258_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4259_neg : (17372373 / 200000000) ≤ -Real.log (500000 / 545373) ∧
    -Real.log (500000 / 545373) ≤ (43430933 / 500000000) := by
  have h := checkLog_sound (w := (45373 / 1045373)) (n := 12)
    (lo := (17372373 / 200000000)) (hi := (43430933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((545373 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(545373 / 500000) = 1/(500000 / 545373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4259 : Bounds (17372373 / 200000000) (43430933 / 500000000) (Real.log (545373 / 500000)) := by
  have h := reflection_log_4259_neg
  have he : Real.log (545373 / 500000) = -Real.log (500000 / 545373) := by
    rw [show ((545373 / 500000) : ℝ) = ((500000 / 545373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4260_neg : (19026159 / 200000000) ≤ -Real.log (454627 / 500000) ∧
    -Real.log (454627 / 500000) ≤ (23782699 / 250000000) := by
  have h := checkLog_sound (w := (45373 / 954627)) (n := 12)
    (lo := (19026159 / 200000000)) (hi := (23782699 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 454627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 454627) = 1/(454627 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4260 : Bounds (-23782699 / 250000000) (-19026159 / 200000000) (Real.log (454627 / 500000)) := by
  have h := reflection_log_4260_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4261_neg : (696589 / 8000000) ≤ -Real.log (1000000 / 1090977) ∧
    -Real.log (1000000 / 1090977) ≤ (43536813 / 500000000) := by
  have h := checkLog_sound (w := (90977 / 2090977)) (n := 12)
    (lo := (696589 / 8000000)) (hi := (43536813 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090977 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090977 / 1000000) = 1/(1000000 / 1090977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4261 : Bounds (696589 / 8000000) (43536813 / 500000000) (Real.log (1090977 / 1000000)) := by
  have h := reflection_log_4261_neg
  have he : Real.log (1090977 / 1000000) = -Real.log (1000000 / 1090977) := by
    rw [show ((1090977 / 1000000) : ℝ) = ((1000000 / 1090977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4262_neg : (47692441 / 500000000) ≤ -Real.log (909023 / 1000000) ∧
    -Real.log (909023 / 1000000) ≤ (95384883 / 1000000000) := by
  have h := checkLog_sound (w := (90977 / 1909023)) (n := 12)
    (lo := (47692441 / 500000000)) (hi := (95384883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909023) = 1/(909023 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4262 : Bounds (-95384883 / 1000000000) (-47692441 / 500000000) (Real.log (909023 / 1000000)) := by
  have h := reflection_log_4262_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4263_neg : (8311257 / 1000000000) ≤ -Real.log (991723185471 / 1000000000000) ∧
    -Real.log (991723185471 / 1000000000000) ≤ (4155629 / 500000000) := by
  have h := checkLog_sound (w := (8276814529 / 1991723185471)) (n := 12)
    (lo := (8311257 / 1000000000)) (hi := (4155629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991723185471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991723185471) = 1/(991723185471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4263 : Bounds (-4155629 / 500000000) (-8311257 / 1000000000) (Real.log (991723185471 / 1000000000000)) := by
  have h := reflection_log_4263_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4264_neg : (826893 / 100000000) ≤ -Real.log (247941290871 / 250000000000) ∧
    -Real.log (247941290871 / 250000000000) ≤ (8268931 / 1000000000) := by
  have h := checkLog_sound (w := (2058709129 / 497941290871)) (n := 12)
    (lo := (826893 / 100000000)) (hi := (8268931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247941290871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247941290871) = 1/(247941290871 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4264 : Bounds (-8268931 / 1000000000) (-826893 / 100000000) (Real.log (247941290871 / 250000000000)) := by
  have h := reflection_log_4264_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4265_neg : (181992661 / 1000000000) ≤ -Real.log (125000000000 / 149950673849) ∧
    -Real.log (125000000000 / 149950673849) ≤ (90996331 / 500000000) := by
  have h := checkLog_sound (w := (24950673849 / 274950673849)) (n := 12)
    (lo := (181992661 / 1000000000)) (hi := (90996331 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149950673849 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149950673849 / 125000000000) = 1/(125000000000 / 149950673849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4265 : Bounds (181992661 / 1000000000) (90996331 / 500000000) (Real.log (149950673849 / 125000000000)) := by
  have h := reflection_log_4265_neg
  have he : Real.log (149950673849 / 125000000000) = -Real.log (125000000000 / 149950673849) := by
    rw [show ((149950673849 / 125000000000) : ℝ) = ((125000000000 / 149950673849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4266_neg : (182458507 / 1000000000) ≤ -Real.log (500000000000 / 600082176139) ∧
    -Real.log (500000000000 / 600082176139) ≤ (45614627 / 250000000) := by
  have h := checkLog_sound (w := (100082176139 / 1100082176139)) (n := 12)
    (lo := (182458507 / 1000000000)) (hi := (45614627 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((600082176139 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(600082176139 / 500000000000) = 1/(500000000000 / 600082176139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4266 : Bounds (182458507 / 1000000000) (45614627 / 250000000) (Real.log (600082176139 / 500000000000)) := by
  have h := reflection_log_4266_neg
  have he : Real.log (600082176139 / 500000000000) = -Real.log (500000000000 / 600082176139) := by
    rw [show ((600082176139 / 500000000000) : ℝ) = ((500000000000 / 600082176139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4267_neg : (365205697 / 1000000000) ≤ -Real.log (500000000000 / 720405174517) ∧
    -Real.log (500000000000 / 720405174517) ≤ (182602849 / 500000000) := by
  have h := checkLog_sound (w := (220405174517 / 1220405174517)) (n := 12)
    (lo := (365205697 / 1000000000)) (hi := (182602849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((720405174517 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(720405174517 / 500000000000) = 1/(500000000000 / 720405174517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4267 : Bounds (365205697 / 1000000000) (182602849 / 500000000) (Real.log (720405174517 / 500000000000)) := by
  have h := reflection_log_4267_neg
  have he : Real.log (720405174517 / 500000000000) = -Real.log (500000000000 / 720405174517) := by
    rw [show ((720405174517 / 500000000000) : ℝ) = ((500000000000 / 720405174517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4268_neg : (91353111 / 250000000) ≤ -Real.log (62500000000 / 90069266447) ∧
    -Real.log (62500000000 / 90069266447) ≤ (73082489 / 200000000) := by
  have h := checkLog_sound (w := (27569266447 / 152569266447)) (n := 12)
    (lo := (91353111 / 250000000)) (hi := (73082489 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90069266447 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90069266447 / 62500000000) = 1/(62500000000 / 90069266447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4268 : Bounds (91353111 / 250000000) (73082489 / 200000000) (Real.log (90069266447 / 62500000000)) := by
  have h := reflection_log_4268_neg
  have he : Real.log (90069266447 / 62500000000) = -Real.log (62500000000 / 90069266447) := by
    rw [show ((90069266447 / 62500000000) : ℝ) = ((62500000000 / 90069266447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4269_neg : (83096087 / 500000000) ≤ -Real.log (625 / 738) ∧
    -Real.log (625 / 738) ≤ (6647687 / 40000000) := by
  have h := checkLog_sound (w := (113 / 1363)) (n := 12)
    (lo := (83096087 / 500000000)) (hi := (6647687 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((738 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(738 / 625) = 1/(625 / 738) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4269 : Bounds (83096087 / 500000000) (6647687 / 40000000) (Real.log (738 / 625)) := by
  have h := reflection_log_4269_neg
  have he : Real.log (738 / 625) = -Real.log (625 / 738) := by
    rw [show ((738 / 625) : ℝ) = ((625 / 738) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4270_neg : (12464189 / 62500000) ≤ -Real.log (512 / 625) ∧
    -Real.log (512 / 625) ≤ (7977081 / 40000000) := by
  have h := checkLog_sound (w := (113 / 1137)) (n := 12)
    (lo := (12464189 / 62500000)) (hi := (7977081 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 512) = 1/(512 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4270 : Bounds (-7977081 / 40000000) (-12464189 / 62500000) (Real.log (512 / 625)) := by
  have h := reflection_log_4270_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4271_neg : (180783 / 1000000000) ≤ -Real.log (625000 / 625113) ∧
    -Real.log (625000 / 625113) ≤ (11299 / 62500000) := by
  have h := checkLog_sound (w := (113 / 1250113)) (n := 12)
    (lo := (180783 / 1000000000)) (hi := (11299 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625113 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625113 / 625000) = 1/(625000 / 625113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4271 : Bounds (180783 / 1000000000) (11299 / 62500000) (Real.log (625113 / 625000)) := by
  have h := reflection_log_4271_neg
  have he : Real.log (625113 / 625000) = -Real.log (625000 / 625113) := by
    rw [show ((625113 / 625000) : ℝ) = ((625000 / 625113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4272_neg : (11301 / 62500000) ≤ -Real.log (624887 / 625000) ∧
    -Real.log (624887 / 625000) ≤ (180817 / 1000000000) := by
  have h := checkLog_sound (w := (113 / 1249887)) (n := 12)
    (lo := (11301 / 62500000)) (hi := (180817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624887) = 1/(624887 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4272 : Bounds (-180817 / 1000000000) (-11301 / 62500000) (Real.log (624887 / 625000)) := by
  have h := reflection_log_4272_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4273_neg : (86908621 / 1000000000) ≤ -Real.log (1000000 / 1090797) ∧
    -Real.log (1000000 / 1090797) ≤ (43454311 / 500000000) := by
  have h := checkLog_sound (w := (90797 / 2090797)) (n := 12)
    (lo := (86908621 / 1000000000)) (hi := (43454311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1090797 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1090797 / 1000000) = 1/(1000000 / 1090797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4273 : Bounds (86908621 / 1000000000) (43454311 / 500000000) (Real.log (1090797 / 1000000)) := by
  have h := reflection_log_4273_neg
  have he : Real.log (1090797 / 1000000) = -Real.log (1000000 / 1090797) := by
    rw [show ((1090797 / 1000000) : ℝ) = ((1000000 / 1090797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4274_neg : (95186887 / 1000000000) ≤ -Real.log (909203 / 1000000) ∧
    -Real.log (909203 / 1000000) ≤ (11898361 / 125000000) := by
  have h := checkLog_sound (w := (90797 / 1909203)) (n := 12)
    (lo := (95186887 / 1000000000)) (hi := (11898361 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 909203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 909203) = 1/(909203 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4274 : Bounds (-11898361 / 125000000) (-95186887 / 1000000000) (Real.log (909203 / 1000000)) := by
  have h := reflection_log_4274_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4275_neg : (87120371 / 1000000000) ≤ -Real.log (250000 / 272757) ∧
    -Real.log (250000 / 272757) ≤ (21780093 / 250000000) := by
  have h := checkLog_sound (w := (22757 / 522757)) (n := 12)
    (lo := (87120371 / 1000000000)) (hi := (21780093 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272757 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(272757 / 250000) = 1/(250000 / 272757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4275 : Bounds (87120371 / 1000000000) (21780093 / 250000000) (Real.log (272757 / 250000)) := by
  have h := reflection_log_4275_neg
  have he : Real.log (272757 / 250000) = -Real.log (250000 / 272757) := by
    rw [show ((272757 / 250000) : ℝ) = ((250000 / 272757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4276_neg : (23860247 / 250000000) ≤ -Real.log (227243 / 250000) ∧
    -Real.log (227243 / 250000) ≤ (95440989 / 1000000000) := by
  have h := checkLog_sound (w := (22757 / 477243)) (n := 12)
    (lo := (23860247 / 250000000)) (hi := (95440989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 227243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 227243) = 1/(227243 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4276 : Bounds (-95440989 / 1000000000) (-23860247 / 250000000) (Real.log (227243 / 250000)) := by
  have h := reflection_log_4276_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4277_neg : (8320617 / 1000000000) ≤ -Real.log (61982118951 / 62500000000) ∧
    -Real.log (61982118951 / 62500000000) ≤ (4160309 / 500000000) := by
  have h := checkLog_sound (w := (517881049 / 124482118951)) (n := 12)
    (lo := (8320617 / 1000000000)) (hi := (4160309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61982118951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61982118951) = 1/(61982118951 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4277 : Bounds (-4160309 / 500000000) (-8320617 / 1000000000) (Real.log (61982118951 / 62500000000)) := by
  have h := reflection_log_4277_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4278_neg : (1655653 / 200000000) ≤ -Real.log (991755904791 / 1000000000000) ∧
    -Real.log (991755904791 / 1000000000000) ≤ (4139133 / 500000000) := by
  have h := checkLog_sound (w := (8244095209 / 1991755904791)) (n := 12)
    (lo := (1655653 / 200000000)) (hi := (4139133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991755904791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991755904791) = 1/(991755904791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4278 : Bounds (-4139133 / 500000000) (-1655653 / 200000000) (Real.log (991755904791 / 1000000000000)) := by
  have h := reflection_log_4278_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4279_neg : (182095509 / 1000000000) ≤ -Real.log (500000000000 / 599864386721) ∧
    -Real.log (500000000000 / 599864386721) ≤ (18209551 / 100000000) := by
  have h := checkLog_sound (w := (99864386721 / 1099864386721)) (n := 12)
    (lo := (182095509 / 1000000000)) (hi := (18209551 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((599864386721 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(599864386721 / 500000000000) = 1/(500000000000 / 599864386721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4279 : Bounds (182095509 / 1000000000) (18209551 / 100000000) (Real.log (599864386721 / 500000000000)) := by
  have h := reflection_log_4279_neg
  have he : Real.log (599864386721 / 500000000000) = -Real.log (500000000000 / 599864386721) := by
    rw [show ((599864386721 / 500000000000) : ℝ) = ((500000000000 / 599864386721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4280_neg : (182561359 / 1000000000) ≤ -Real.log (250000000000 / 300071949411) ∧
    -Real.log (250000000000 / 300071949411) ≤ (2282017 / 12500000) := by
  have h := checkLog_sound (w := (50071949411 / 550071949411)) (n := 12)
    (lo := (182561359 / 1000000000)) (hi := (2282017 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300071949411 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300071949411 / 250000000000) = 1/(250000000000 / 300071949411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4280 : Bounds (182561359 / 1000000000) (2282017 / 12500000) (Real.log (300071949411 / 250000000000)) := by
  have h := reflection_log_4280_neg
  have he : Real.log (300071949411 / 250000000000) = -Real.log (250000000000 / 300071949411) := by
    rw [show ((300071949411 / 250000000000) : ℝ) = ((250000000000 / 300071949411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4281_neg : (91353111 / 250000000) ≤ -Real.log (20000000000 / 28822165263) ∧
    -Real.log (20000000000 / 28822165263) ≤ (73082489 / 200000000) := by
  have h := checkLog_sound (w := (8822165263 / 48822165263)) (n := 12)
    (lo := (91353111 / 250000000)) (hi := (73082489 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28822165263 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28822165263 / 20000000000) = 1/(20000000000 / 28822165263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4281 : Bounds (91353111 / 250000000) (73082489 / 200000000) (Real.log (28822165263 / 20000000000)) := by
  have h := reflection_log_4281_neg
  have he : Real.log (28822165263 / 20000000000) = -Real.log (20000000000 / 28822165263) := by
    rw [show ((28822165263 / 20000000000) : ℝ) = ((20000000000 / 28822165263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4282_neg : (365619199 / 1000000000) ≤ -Real.log (256 / 369) ∧
    -Real.log (256 / 369) ≤ (28564 / 78125) := by
  have h := checkLog_sound (w := (113 / 625)) (n := 12)
    (lo := (365619199 / 1000000000)) (hi := (28564 / 78125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369 / 256) = 1/(256 / 369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4282 : Bounds (365619199 / 1000000000) (28564 / 78125) (Real.log (369 / 256)) := by
  have h := reflection_log_4282_neg
  have he : Real.log (369 / 256) = -Real.log (256 / 369) := by
    rw [show ((369 / 256) : ℝ) = ((256 / 369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4283_neg : (166276859 / 1000000000) ≤ -Real.log (10000 / 11809) ∧
    -Real.log (10000 / 11809) ≤ (8313843 / 50000000) := by
  have h := checkLog_sound (w := (1809 / 21809)) (n := 12)
    (lo := (166276859 / 1000000000)) (hi := (8313843 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11809 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11809 / 10000) = 1/(10000 / 11809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4283 : Bounds (166276859 / 1000000000) (8313843 / 50000000) (Real.log (11809 / 10000)) := by
  have h := reflection_log_4283_neg
  have he : Real.log (11809 / 10000) = -Real.log (10000 / 11809) := by
    rw [show ((11809 / 10000) : ℝ) = ((10000 / 11809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4284_neg : (99774551 / 500000000) ≤ -Real.log (8191 / 10000) ∧
    -Real.log (8191 / 10000) ≤ (199549103 / 1000000000) := by
  have h := checkLog_sound (w := (1809 / 18191)) (n := 12)
    (lo := (99774551 / 500000000)) (hi := (199549103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8191) = 1/(8191 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4284 : Bounds (-199549103 / 1000000000) (-99774551 / 500000000) (Real.log (8191 / 10000)) := by
  have h := reflection_log_4284_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4285_neg : (180883 / 1000000000) ≤ -Real.log (10000000 / 10001809) ∧
    -Real.log (10000000 / 10001809) ≤ (45221 / 250000000) := by
  have h := checkLog_sound (w := (1809 / 20001809)) (n := 12)
    (lo := (180883 / 1000000000)) (hi := (45221 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001809 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001809 / 10000000) = 1/(10000000 / 10001809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4285 : Bounds (180883 / 1000000000) (45221 / 250000000) (Real.log (10001809 / 10000000)) := by
  have h := reflection_log_4285_neg
  have he : Real.log (10001809 / 10000000) = -Real.log (10000000 / 10001809) := by
    rw [show ((10001809 / 10000000) : ℝ) = ((10000000 / 10001809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4286_neg : (45229 / 250000000) ≤ -Real.log (9998191 / 10000000) ∧
    -Real.log (9998191 / 10000000) ≤ (180917 / 1000000000) := by
  have h := checkLog_sound (w := (1809 / 19998191)) (n := 12)
    (lo := (45229 / 250000000)) (hi := (180917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998191) = 1/(9998191 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4286 : Bounds (-180917 / 1000000000) (-45229 / 250000000) (Real.log (9998191 / 10000000)) := by
  have h := reflection_log_4286_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_4287_neg : (695643 / 8000000) ≤ -Real.log (31250 / 34089) ∧
    -Real.log (31250 / 34089) ≤ (5434711 / 62500000) := by
  have h := checkLog_sound (w := (2839 / 65339)) (n := 12)
    (lo := (695643 / 8000000)) (hi := (5434711 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34089 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34089 / 31250) = 1/(31250 / 34089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4287 : Bounds (695643 / 8000000) (5434711 / 62500000) (Real.log (34089 / 31250)) := by
  have h := reflection_log_4287_neg
  have he : Real.log (34089 / 31250) = -Real.log (31250 / 34089) := by
    rw [show ((34089 / 31250) : ℝ) = ((31250 / 34089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
