import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8960_neg : (19003263 / 1000000000) ≤ -Real.log (6132351 / 6250000) ∧
    -Real.log (6132351 / 6250000) ≤ (148463 / 7812500) := by
  have h := checkLog_sound (w := (117649 / 12382351)) (n := 12)
    (lo := (19003263 / 1000000000)) (hi := (148463 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250000 / 6132351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250000 / 6132351) = 1/(6132351 / 6250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8960 : Bounds (-148463 / 7812500) (-19003263 / 1000000000) (Real.log (6132351 / 6250000)) := by
  have h := reflection_log_8960_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8961_neg : (55228293 / 200000000) ≤ -Real.log (500000000000 / 659017153453) ∧
    -Real.log (500000000000 / 659017153453) ≤ (138070733 / 500000000) := by
  have h := checkLog_sound (w := (159017153453 / 1159017153453)) (n := 12)
    (lo := (55228293 / 200000000)) (hi := (138070733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((659017153453 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(659017153453 / 500000000000) = 1/(500000000000 / 659017153453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8961 : Bounds (55228293 / 200000000) (138070733 / 500000000) (Real.log (659017153453 / 500000000000)) := by
  have h := reflection_log_8961_neg
  have he : Real.log (659017153453 / 500000000000) = -Real.log (500000000000 / 659017153453) := by
    rw [show ((659017153453 / 500000000000) : ℝ) = ((500000000000 / 659017153453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8962_neg : (138609921 / 500000000) ≤ -Real.log (250000000000 / 329864103049) ∧
    -Real.log (250000000000 / 329864103049) ≤ (277219843 / 1000000000) := by
  have h := checkLog_sound (w := (79864103049 / 579864103049)) (n := 12)
    (lo := (138609921 / 500000000)) (hi := (277219843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329864103049 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329864103049 / 250000000000) = 1/(250000000000 / 329864103049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8962 : Bounds (138609921 / 500000000) (277219843 / 1000000000) (Real.log (329864103049 / 250000000000)) := by
  have h := reflection_log_8962_neg
  have he : Real.log (329864103049 / 250000000000) = -Real.log (250000000000 / 329864103049) := by
    rw [show ((329864103049 / 250000000000) : ℝ) = ((250000000000 / 329864103049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8963_neg : (555885539 / 1000000000) ≤ -Real.log (250000000000 / 435871056241) ∧
    -Real.log (250000000000 / 435871056241) ≤ (27794277 / 50000000) := by
  have h := checkLog_sound (w := (185871056241 / 685871056241)) (n := 12)
    (lo := (555885539 / 1000000000)) (hi := (27794277 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((435871056241 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(435871056241 / 250000000000) = 1/(250000000000 / 435871056241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8963 : Bounds (555885539 / 1000000000) (27794277 / 50000000) (Real.log (435871056241 / 250000000000)) := by
  have h := reflection_log_8963_neg
  have he : Real.log (435871056241 / 250000000000) = -Real.log (250000000000 / 435871056241) := by
    rw [show ((435871056241 / 250000000000) : ℝ) = ((250000000000 / 435871056241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8964_neg : (556964959 / 1000000000) ≤ -Real.log (31250000000 / 54542724777) ∧
    -Real.log (31250000000 / 54542724777) ≤ (3481031 / 6250000) := by
  have h := checkLog_sound (w := (23292724777 / 85792724777)) (n := 12)
    (lo := (556964959 / 1000000000)) (hi := (3481031 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54542724777 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54542724777 / 31250000000) = 1/(31250000000 / 54542724777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8964 : Bounds (556964959 / 1000000000) (3481031 / 6250000) (Real.log (54542724777 / 31250000000)) := by
  have h := reflection_log_8964_neg
  have he : Real.log (54542724777 / 31250000000) = -Real.log (31250000000 / 54542724777) := by
    rw [show ((54542724777 / 31250000000) : ℝ) = ((31250000000 / 54542724777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8965_neg : (1879613 / 7812500) ≤ -Real.log (125 / 159) ∧
    -Real.log (125 / 159) ≤ (48118093 / 200000000) := by
  have h := checkLog_sound (w := (17 / 142)) (n := 12)
    (lo := (1879613 / 7812500)) (hi := (48118093 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159 / 125) = 1/(125 / 159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8965 : Bounds (1879613 / 7812500) (48118093 / 200000000) (Real.log (159 / 125)) := by
  have h := reflection_log_8965_neg
  have he : Real.log (159 / 125) = -Real.log (125 / 159) := by
    rw [show ((159 / 125) : ℝ) = ((125 / 159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8966_neg : (31745423 / 100000000) ≤ -Real.log (91 / 125) ∧
    -Real.log (91 / 125) ≤ (317454231 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 108)) (n := 12)
    (lo := (31745423 / 100000000)) (hi := (317454231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 91) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 91) = 1/(91 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8966 : Bounds (-317454231 / 1000000000) (-31745423 / 100000000) (Real.log (91 / 125)) := by
  have h := reflection_log_8966_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8967_neg : (271963 / 1000000000) ≤ -Real.log (62500 / 62517) ∧
    -Real.log (62500 / 62517) ≤ (67991 / 250000000) := by
  have h := checkLog_sound (w := (17 / 125017)) (n := 12)
    (lo := (271963 / 1000000000)) (hi := (67991 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62517 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62517 / 62500) = 1/(62500 / 62517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8967 : Bounds (271963 / 1000000000) (67991 / 250000000) (Real.log (62517 / 62500)) := by
  have h := reflection_log_8967_neg
  have he : Real.log (62517 / 62500) = -Real.log (62500 / 62517) := by
    rw [show ((62517 / 62500) : ℝ) = ((62500 / 62517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8968_neg : (68009 / 250000000) ≤ -Real.log (62483 / 62500) ∧
    -Real.log (62483 / 62500) ≤ (272037 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 124983)) (n := 12)
    (lo := (68009 / 250000000)) (hi := (272037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62483) = 1/(62483 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8968 : Bounds (-272037 / 1000000000) (-68009 / 250000000) (Real.log (62483 / 62500)) := by
  have h := reflection_log_8968_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8969_neg : (64398853 / 500000000) ≤ -Real.log (50000 / 56873) ∧
    -Real.log (50000 / 56873) ≤ (128797707 / 1000000000) := by
  have h := checkLog_sound (w := (6873 / 106873)) (n := 12)
    (lo := (64398853 / 500000000)) (hi := (128797707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56873 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(56873 / 50000) = 1/(50000 / 56873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8969 : Bounds (64398853 / 500000000) (128797707 / 1000000000) (Real.log (56873 / 50000)) := by
  have h := reflection_log_8969_neg
  have he : Real.log (56873 / 50000) = -Real.log (50000 / 56873) := by
    rw [show ((56873 / 50000) : ℝ) = ((50000 / 56873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8970_neg : (73936877 / 500000000) ≤ -Real.log (43127 / 50000) ∧
    -Real.log (43127 / 50000) ≤ (29574751 / 200000000) := by
  have h := checkLog_sound (w := (6873 / 93127)) (n := 12)
    (lo := (73936877 / 500000000)) (hi := (29574751 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 43127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 43127) = 1/(43127 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8970 : Bounds (-29574751 / 200000000) (-73936877 / 500000000) (Real.log (43127 / 50000)) := by
  have h := reflection_log_8970_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8971_neg : (32315887 / 250000000) ≤ -Real.log (100000 / 113799) ∧
    -Real.log (100000 / 113799) ≤ (129263549 / 1000000000) := by
  have h := checkLog_sound (w := (13799 / 213799)) (n := 12)
    (lo := (32315887 / 250000000)) (hi := (129263549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((113799 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(113799 / 100000) = 1/(100000 / 113799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8971 : Bounds (32315887 / 250000000) (129263549 / 1000000000) (Real.log (113799 / 100000)) := by
  have h := reflection_log_8971_neg
  have he : Real.log (113799 / 100000) = -Real.log (100000 / 113799) := by
    rw [show ((113799 / 100000) : ℝ) = ((100000 / 113799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8972_neg : (148488407 / 1000000000) ≤ -Real.log (86201 / 100000) ∧
    -Real.log (86201 / 100000) ≤ (18561051 / 125000000) := by
  have h := checkLog_sound (w := (13799 / 186201)) (n := 12)
    (lo := (148488407 / 1000000000)) (hi := (18561051 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 86201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 86201) = 1/(86201 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8972 : Bounds (-18561051 / 125000000) (-148488407 / 1000000000) (Real.log (86201 / 100000)) := by
  have h := reflection_log_8972_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8973_neg : (19224859 / 1000000000) ≤ -Real.log (9809587599 / 10000000000) ∧
    -Real.log (9809587599 / 10000000000) ≤ (961243 / 50000000) := by
  have h := checkLog_sound (w := (190412401 / 19809587599)) (n := 12)
    (lo := (19224859 / 1000000000)) (hi := (961243 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9809587599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9809587599) = 1/(9809587599 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8973 : Bounds (-961243 / 50000000) (-19224859 / 1000000000) (Real.log (9809587599 / 10000000000)) := by
  have h := reflection_log_8973_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8974_neg : (19076047 / 1000000000) ≤ -Real.log (2452761871 / 2500000000) ∧
    -Real.log (2452761871 / 2500000000) ≤ (1192253 / 62500000) := by
  have h := checkLog_sound (w := (47238129 / 4952761871)) (n := 12)
    (lo := (19076047 / 1000000000)) (hi := (1192253 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2452761871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2452761871) = 1/(2452761871 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8974 : Bounds (-1192253 / 62500000) (-19076047 / 1000000000) (Real.log (2452761871 / 2500000000)) := by
  have h := reflection_log_8974_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8975_neg : (13833573 / 50000000) ≤ -Real.log (125000000000 / 164841630533) ∧
    -Real.log (125000000000 / 164841630533) ≤ (276671461 / 1000000000) := by
  have h := checkLog_sound (w := (39841630533 / 289841630533)) (n := 12)
    (lo := (13833573 / 50000000)) (hi := (276671461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164841630533 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164841630533 / 125000000000) = 1/(125000000000 / 164841630533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8975 : Bounds (13833573 / 50000000) (276671461 / 1000000000) (Real.log (164841630533 / 125000000000)) := by
  have h := reflection_log_8975_neg
  have he : Real.log (164841630533 / 125000000000) = -Real.log (125000000000 / 164841630533) := by
    rw [show ((164841630533 / 125000000000) : ℝ) = ((125000000000 / 164841630533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8976_neg : (55550391 / 200000000) ≤ -Real.log (125000000000 / 165019837357) ∧
    -Real.log (125000000000 / 165019837357) ≤ (69437989 / 250000000) := by
  have h := checkLog_sound (w := (40019837357 / 290019837357)) (n := 12)
    (lo := (55550391 / 200000000)) (hi := (69437989 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165019837357 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165019837357 / 125000000000) = 1/(125000000000 / 165019837357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8976 : Bounds (55550391 / 200000000) (69437989 / 250000000) (Real.log (165019837357 / 125000000000)) := by
  have h := reflection_log_8976_neg
  have he : Real.log (165019837357 / 125000000000) = -Real.log (125000000000 / 165019837357) := by
    rw [show ((165019837357 / 125000000000) : ℝ) = ((125000000000 / 165019837357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8977_neg : (556964959 / 1000000000) ≤ -Real.log (500000000000 / 872683596431) ∧
    -Real.log (500000000000 / 872683596431) ≤ (3481031 / 6250000) := by
  have h := checkLog_sound (w := (372683596431 / 1372683596431)) (n := 12)
    (lo := (556964959 / 1000000000)) (hi := (3481031 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((872683596431 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(872683596431 / 500000000000) = 1/(500000000000 / 872683596431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8977 : Bounds (556964959 / 1000000000) (3481031 / 6250000) (Real.log (872683596431 / 500000000000)) := by
  have h := reflection_log_8977_neg
  have he : Real.log (872683596431 / 500000000000) = -Real.log (500000000000 / 872683596431) := by
    rw [show ((872683596431 / 500000000000) : ℝ) = ((500000000000 / 872683596431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8978_neg : (111608939 / 200000000) ≤ -Real.log (500000000000 / 873626373627) ∧
    -Real.log (500000000000 / 873626373627) ≤ (69755587 / 125000000) := by
  have h := checkLog_sound (w := (373626373627 / 1373626373627)) (n := 12)
    (lo := (111608939 / 200000000)) (hi := (69755587 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((873626373627 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(873626373627 / 500000000000) = 1/(500000000000 / 873626373627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8978 : Bounds (111608939 / 200000000) (69755587 / 125000000) (Real.log (873626373627 / 500000000000)) := by
  have h := reflection_log_8978_neg
  have he : Real.log (873626373627 / 500000000000) = -Real.log (500000000000 / 873626373627) := by
    rw [show ((873626373627 / 500000000000) : ℝ) = ((500000000000 / 873626373627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8979_neg : (240983469 / 1000000000) ≤ -Real.log (400 / 509) ∧
    -Real.log (400 / 509) ≤ (24098347 / 100000000) := by
  have h := checkLog_sound (w := (109 / 909)) (n := 12)
    (lo := (240983469 / 1000000000)) (hi := (24098347 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((509 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(509 / 400) = 1/(400 / 509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8979 : Bounds (240983469 / 1000000000) (24098347 / 100000000) (Real.log (509 / 400)) := by
  have h := reflection_log_8979_neg
  have he : Real.log (509 / 400) = -Real.log (400 / 509) := by
    rw [show ((509 / 400) : ℝ) = ((400 / 509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8980_neg : (318141279 / 1000000000) ≤ -Real.log (291 / 400) ∧
    -Real.log (291 / 400) ≤ (1988383 / 6250000) := by
  have h := checkLog_sound (w := (109 / 691)) (n := 12)
    (lo := (318141279 / 1000000000)) (hi := (1988383 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 291) = 1/(291 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8980 : Bounds (-1988383 / 6250000) (-318141279 / 1000000000) (Real.log (291 / 400)) := by
  have h := reflection_log_8980_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8981_neg : (136231 / 500000000) ≤ -Real.log (400000 / 400109) ∧
    -Real.log (400000 / 400109) ≤ (272463 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 800109)) (n := 12)
    (lo := (136231 / 500000000)) (hi := (272463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400109 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400109 / 400000) = 1/(400000 / 400109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8981 : Bounds (136231 / 500000000) (272463 / 1000000000) (Real.log (400109 / 400000)) := by
  have h := reflection_log_8981_neg
  have he : Real.log (400109 / 400000) = -Real.log (400000 / 400109) := by
    rw [show ((400109 / 400000) : ℝ) = ((400000 / 400109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8982_neg : (272537 / 1000000000) ≤ -Real.log (399891 / 400000) ∧
    -Real.log (399891 / 400000) ≤ (136269 / 500000000) := by
  have h := checkLog_sound (w := (109 / 799891)) (n := 12)
    (lo := (272537 / 1000000000)) (hi := (136269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399891) = 1/(399891 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8982 : Bounds (-136269 / 500000000) (-272537 / 1000000000) (Real.log (399891 / 400000)) := by
  have h := reflection_log_8982_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8983_neg : (129026259 / 1000000000) ≤ -Real.log (25000 / 28443) ∧
    -Real.log (25000 / 28443) ≤ (6451313 / 50000000) := by
  have h := checkLog_sound (w := (3443 / 53443)) (n := 12)
    (lo := (129026259 / 1000000000)) (hi := (6451313 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28443 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28443 / 25000) = 1/(25000 / 28443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8983 : Bounds (129026259 / 1000000000) (6451313 / 50000000) (Real.log (28443 / 25000)) := by
  have h := reflection_log_8983_neg
  have he : Real.log (28443 / 25000) = -Real.log (25000 / 28443) := by
    rw [show ((28443 / 25000) : ℝ) = ((25000 / 28443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8984_neg : (29635047 / 200000000) ≤ -Real.log (21557 / 25000) ∧
    -Real.log (21557 / 25000) ≤ (37043809 / 250000000) := by
  have h := checkLog_sound (w := (3443 / 46557)) (n := 12)
    (lo := (29635047 / 200000000)) (hi := (37043809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 21557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 21557) = 1/(21557 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8984 : Bounds (-37043809 / 250000000) (-29635047 / 200000000) (Real.log (21557 / 25000)) := by
  have h := reflection_log_8984_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8985_neg : (25898399 / 200000000) ≤ -Real.log (4000 / 4553) ∧
    -Real.log (4000 / 4553) ≤ (32372999 / 250000000) := by
  have h := checkLog_sound (w := (553 / 8553)) (n := 12)
    (lo := (25898399 / 200000000)) (hi := (32372999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4553 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4553 / 4000) = 1/(4000 / 4553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8985 : Bounds (25898399 / 200000000) (32372999 / 250000000) (Real.log (4553 / 4000)) := by
  have h := reflection_log_8985_neg
  have he : Real.log (4553 / 4000) = -Real.log (4000 / 4553) := by
    rw [show ((4553 / 4000) : ℝ) = ((4000 / 4553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8986_neg : (148790073 / 1000000000) ≤ -Real.log (3447 / 4000) ∧
    -Real.log (3447 / 4000) ≤ (74395037 / 500000000) := by
  have h := checkLog_sound (w := (553 / 7447)) (n := 12)
    (lo := (148790073 / 1000000000)) (hi := (74395037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 3447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000 / 3447) = 1/(3447 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8986 : Bounds (-74395037 / 500000000) (-148790073 / 1000000000) (Real.log (3447 / 4000)) := by
  have h := reflection_log_8986_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8987_neg : (9649039 / 500000000) ≤ -Real.log (15694191 / 16000000) ∧
    -Real.log (15694191 / 16000000) ≤ (19298079 / 1000000000) := by
  have h := checkLog_sound (w := (305809 / 31694191)) (n := 12)
    (lo := (9649039 / 500000000)) (hi := (19298079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16000000 / 15694191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16000000 / 15694191) = 1/(15694191 / 16000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8987 : Bounds (-19298079 / 1000000000) (-9649039 / 500000000) (Real.log (15694191 / 16000000)) := by
  have h := reflection_log_8987_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8988_neg : (765959 / 40000000) ≤ -Real.log (613145751 / 625000000) ∧
    -Real.log (613145751 / 625000000) ≤ (1196811 / 62500000) := by
  have h := checkLog_sound (w := (11854249 / 1238145751)) (n := 12)
    (lo := (765959 / 40000000)) (hi := (1196811 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 613145751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 613145751) = 1/(613145751 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8988 : Bounds (-1196811 / 62500000) (-765959 / 40000000) (Real.log (613145751 / 625000000)) := by
  have h := reflection_log_8988_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8989_neg : (138600747 / 500000000) ≤ -Real.log (250000000000 / 329858050749) ∧
    -Real.log (250000000000 / 329858050749) ≤ (55440299 / 200000000) := by
  have h := checkLog_sound (w := (79858050749 / 579858050749)) (n := 12)
    (lo := (138600747 / 500000000)) (hi := (55440299 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329858050749 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329858050749 / 250000000000) = 1/(250000000000 / 329858050749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8989 : Bounds (138600747 / 500000000) (55440299 / 200000000) (Real.log (329858050749 / 250000000000)) := by
  have h := reflection_log_8989_neg
  have he : Real.log (329858050749 / 250000000000) = -Real.log (250000000000 / 329858050749) := by
    rw [show ((329858050749 / 250000000000) : ℝ) = ((250000000000 / 329858050749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8990_neg : (69570517 / 250000000) ≤ -Real.log (500000000000 / 660429358863) ∧
    -Real.log (500000000000 / 660429358863) ≤ (278282069 / 1000000000) := by
  have h := checkLog_sound (w := (160429358863 / 1160429358863)) (n := 12)
    (lo := (69570517 / 250000000)) (hi := (278282069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((660429358863 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(660429358863 / 500000000000) = 1/(500000000000 / 660429358863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8990 : Bounds (69570517 / 250000000) (278282069 / 1000000000) (Real.log (660429358863 / 500000000000)) := by
  have h := reflection_log_8990_neg
  have he : Real.log (660429358863 / 500000000000) = -Real.log (500000000000 / 660429358863) := by
    rw [show ((660429358863 / 500000000000) : ℝ) = ((500000000000 / 660429358863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8991_neg : (111608939 / 200000000) ≤ -Real.log (250000000000 / 436813186813) ∧
    -Real.log (250000000000 / 436813186813) ≤ (69755587 / 125000000) := by
  have h := checkLog_sound (w := (186813186813 / 686813186813)) (n := 12)
    (lo := (111608939 / 200000000)) (hi := (69755587 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((436813186813 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(436813186813 / 250000000000) = 1/(250000000000 / 436813186813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8991 : Bounds (111608939 / 200000000) (69755587 / 125000000) (Real.log (436813186813 / 250000000000)) := by
  have h := reflection_log_8991_neg
  have he : Real.log (436813186813 / 250000000000) = -Real.log (250000000000 / 436813186813) := by
    rw [show ((436813186813 / 250000000000) : ℝ) = ((250000000000 / 436813186813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8992_neg : (559124749 / 1000000000) ≤ -Real.log (31250000000 / 54660652921) ∧
    -Real.log (31250000000 / 54660652921) ≤ (2236499 / 4000000) := by
  have h := checkLog_sound (w := (23410652921 / 85910652921)) (n := 12)
    (lo := (559124749 / 1000000000)) (hi := (2236499 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54660652921 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54660652921 / 31250000000) = 1/(31250000000 / 54660652921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8992 : Bounds (559124749 / 1000000000) (2236499 / 4000000) (Real.log (54660652921 / 31250000000)) := by
  have h := reflection_log_8992_neg
  have he : Real.log (54660652921 / 31250000000) = -Real.log (31250000000 / 54660652921) := by
    rw [show ((54660652921 / 31250000000) : ℝ) = ((31250000000 / 54660652921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8993_neg : (241376319 / 1000000000) ≤ -Real.log (1000 / 1273) ∧
    -Real.log (1000 / 1273) ≤ (754301 / 3125000) := by
  have h := checkLog_sound (w := (273 / 2273)) (n := 12)
    (lo := (241376319 / 1000000000)) (hi := (754301 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1273 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1273 / 1000) = 1/(1000 / 1273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8993 : Bounds (241376319 / 1000000000) (754301 / 3125000) (Real.log (1273 / 1000)) := by
  have h := reflection_log_8993_neg
  have he : Real.log (1273 / 1000) = -Real.log (1000 / 1273) := by
    rw [show ((1273 / 1000) : ℝ) = ((1000 / 1273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8994_neg : (318828801 / 1000000000) ≤ -Real.log (727 / 1000) ∧
    -Real.log (727 / 1000) ≤ (159414401 / 500000000) := by
  have h := checkLog_sound (w := (273 / 1727)) (n := 12)
    (lo := (318828801 / 1000000000)) (hi := (159414401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 727) = 1/(727 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8994 : Bounds (-159414401 / 500000000) (-318828801 / 1000000000) (Real.log (727 / 1000)) := by
  have h := reflection_log_8994_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8995_neg : (136481 / 500000000) ≤ -Real.log (1000000 / 1000273) ∧
    -Real.log (1000000 / 1000273) ≤ (272963 / 1000000000) := by
  have h := checkLog_sound (w := (273 / 2000273)) (n := 12)
    (lo := (136481 / 500000000)) (hi := (272963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000273 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000273 / 1000000) = 1/(1000000 / 1000273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8995 : Bounds (136481 / 500000000) (272963 / 1000000000) (Real.log (1000273 / 1000000)) := by
  have h := reflection_log_8995_neg
  have he : Real.log (1000273 / 1000000) = -Real.log (1000000 / 1000273) := by
    rw [show ((1000273 / 1000000) : ℝ) = ((1000000 / 1000273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8996_neg : (273037 / 1000000000) ≤ -Real.log (999727 / 1000000) ∧
    -Real.log (999727 / 1000000) ≤ (136519 / 500000000) := by
  have h := checkLog_sound (w := (273 / 1999727)) (n := 12)
    (lo := (273037 / 1000000000)) (hi := (136519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999727) = 1/(999727 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8996 : Bounds (-136519 / 500000000) (-273037 / 1000000000) (Real.log (999727 / 1000000)) := by
  have h := reflection_log_8996_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8997_neg : (129255639 / 1000000000) ≤ -Real.log (1000000 / 1137981) ∧
    -Real.log (1000000 / 1137981) ≤ (3231391 / 25000000) := by
  have h := checkLog_sound (w := (137981 / 2137981)) (n := 12)
    (lo := (129255639 / 1000000000)) (hi := (3231391 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1137981 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1137981 / 1000000) = 1/(1000000 / 1137981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8997 : Bounds (129255639 / 1000000000) (3231391 / 25000000) (Real.log (1137981 / 1000000)) := by
  have h := reflection_log_8997_neg
  have he : Real.log (1137981 / 1000000) = -Real.log (1000000 / 1137981) := by
    rw [show ((1137981 / 1000000) : ℝ) = ((1000000 / 1137981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8998_neg : (74238983 / 500000000) ≤ -Real.log (862019 / 1000000) ∧
    -Real.log (862019 / 1000000) ≤ (148477967 / 1000000000) := by
  have h := checkLog_sound (w := (137981 / 1862019)) (n := 12)
    (lo := (74238983 / 500000000)) (hi := (148477967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 862019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 862019) = 1/(862019 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8998 : Bounds (-148477967 / 1000000000) (-74238983 / 500000000) (Real.log (862019 / 1000000)) := by
  have h := reflection_log_8998_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8999_neg : (32430317 / 250000000) ≤ -Real.log (1000000 / 1138511) ∧
    -Real.log (1000000 / 1138511) ≤ (129721269 / 1000000000) := by
  have h := checkLog_sound (w := (138511 / 2138511)) (n := 12)
    (lo := (32430317 / 250000000)) (hi := (129721269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1138511 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1138511 / 1000000) = 1/(1000000 / 1138511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8999 : Bounds (32430317 / 250000000) (129721269 / 1000000000) (Real.log (1138511 / 1000000)) := by
  have h := reflection_log_8999_neg
  have he : Real.log (1138511 / 1000000) = -Real.log (1000000 / 1138511) := by
    rw [show ((1138511 / 1000000) : ℝ) = ((1000000 / 1138511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9000_neg : (149092991 / 1000000000) ≤ -Real.log (861489 / 1000000) ∧
    -Real.log (861489 / 1000000) ≤ (1164789 / 7812500) := by
  have h := checkLog_sound (w := (138511 / 1861489)) (n := 12)
    (lo := (149092991 / 1000000000)) (hi := (1164789 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 861489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 861489) = 1/(861489 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9000 : Bounds (-1164789 / 7812500) (-149092991 / 1000000000) (Real.log (861489 / 1000000)) := by
  have h := reflection_log_9000_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9001_neg : (19371723 / 1000000000) ≤ -Real.log (980814702879 / 1000000000000) ∧
    -Real.log (980814702879 / 1000000000000) ≤ (4842931 / 250000000) := by
  have h := checkLog_sound (w := (19185297121 / 1980814702879)) (n := 12)
    (lo := (19371723 / 1000000000)) (hi := (4842931 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980814702879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980814702879) = 1/(980814702879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9001 : Bounds (-4842931 / 250000000) (-19371723 / 1000000000) (Real.log (980814702879 / 1000000000000)) := by
  have h := reflection_log_9001_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9002_neg : (19222327 / 1000000000) ≤ -Real.log (980961243639 / 1000000000000) ∧
    -Real.log (980961243639 / 1000000000000) ≤ (2402791 / 125000000) := by
  have h := checkLog_sound (w := (19038756361 / 1980961243639)) (n := 12)
    (lo := (19222327 / 1000000000)) (hi := (2402791 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980961243639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980961243639) = 1/(980961243639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9002 : Bounds (-2402791 / 125000000) (-19222327 / 1000000000) (Real.log (980961243639 / 1000000000000)) := by
  have h := reflection_log_9002_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9003_neg : (138866803 / 500000000) ≤ -Real.log (500000000000 / 660067237497) ∧
    -Real.log (500000000000 / 660067237497) ≤ (277733607 / 1000000000) := by
  have h := checkLog_sound (w := (160067237497 / 1160067237497)) (n := 12)
    (lo := (138866803 / 500000000)) (hi := (277733607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((660067237497 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(660067237497 / 500000000000) = 1/(500000000000 / 660067237497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9003 : Bounds (138866803 / 500000000) (277733607 / 1000000000) (Real.log (660067237497 / 500000000000)) := by
  have h := reflection_log_9003_neg
  have he : Real.log (660067237497 / 500000000000) = -Real.log (500000000000 / 660067237497) := by
    rw [show ((660067237497 / 500000000000) : ℝ) = ((500000000000 / 660067237497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9004_neg : (278814259 / 1000000000) ≤ -Real.log (500000000000 / 660780926977) ∧
    -Real.log (500000000000 / 660780926977) ≤ (13940713 / 50000000) := by
  have h := checkLog_sound (w := (160780926977 / 1160780926977)) (n := 12)
    (lo := (278814259 / 1000000000)) (hi := (13940713 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((660780926977 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(660780926977 / 500000000000) = 1/(500000000000 / 660780926977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9004 : Bounds (278814259 / 1000000000) (13940713 / 50000000) (Real.log (660780926977 / 500000000000)) := by
  have h := reflection_log_9004_neg
  have he : Real.log (660780926977 / 500000000000) = -Real.log (500000000000 / 660780926977) := by
    rw [show ((660780926977 / 500000000000) : ℝ) = ((500000000000 / 660780926977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9005_neg : (559124749 / 1000000000) ≤ -Real.log (100000000000 / 174914089347) ∧
    -Real.log (100000000000 / 174914089347) ≤ (2236499 / 4000000) := by
  have h := checkLog_sound (w := (74914089347 / 274914089347)) (n := 12)
    (lo := (559124749 / 1000000000)) (hi := (2236499 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((174914089347 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(174914089347 / 100000000000) = 1/(100000000000 / 174914089347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9005 : Bounds (559124749 / 1000000000) (2236499 / 4000000) (Real.log (174914089347 / 100000000000)) := by
  have h := reflection_log_9005_neg
  have he : Real.log (174914089347 / 100000000000) = -Real.log (100000000000 / 174914089347) := by
    rw [show ((174914089347 / 100000000000) : ℝ) = ((100000000000 / 174914089347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9006_neg : (560205121 / 1000000000) ≤ -Real.log (7812500000 / 13679934663) ∧
    -Real.log (7812500000 / 13679934663) ≤ (280102561 / 500000000) := by
  have h := checkLog_sound (w := (5867434663 / 21492434663)) (n := 12)
    (lo := (560205121 / 1000000000)) (hi := (280102561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13679934663 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13679934663 / 7812500000) = 1/(7812500000 / 13679934663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9006 : Bounds (560205121 / 1000000000) (280102561 / 500000000) (Real.log (13679934663 / 7812500000)) := by
  have h := reflection_log_9006_neg
  have he : Real.log (13679934663 / 7812500000) = -Real.log (7812500000 / 13679934663) := by
    rw [show ((13679934663 / 7812500000) : ℝ) = ((7812500000 / 13679934663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9007_neg : (48353803 / 200000000) ≤ -Real.log (2000 / 2547) ∧
    -Real.log (2000 / 2547) ≤ (30221127 / 125000000) := by
  have h := checkLog_sound (w := (547 / 4547)) (n := 12)
    (lo := (48353803 / 200000000)) (hi := (30221127 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2547 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2547 / 2000) = 1/(2000 / 2547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9007 : Bounds (48353803 / 200000000) (30221127 / 125000000) (Real.log (2547 / 2000)) := by
  have h := reflection_log_9007_neg
  have he : Real.log (2547 / 2000) = -Real.log (2000 / 2547) := by
    rw [show ((2547 / 2000) : ℝ) = ((2000 / 2547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9008_neg : (63903359 / 200000000) ≤ -Real.log (1453 / 2000) ∧
    -Real.log (1453 / 2000) ≤ (79879199 / 250000000) := by
  have h := checkLog_sound (w := (547 / 3453)) (n := 12)
    (lo := (63903359 / 200000000)) (hi := (79879199 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1453) = 1/(1453 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9008 : Bounds (-79879199 / 250000000) (-63903359 / 200000000) (Real.log (1453 / 2000)) := by
  have h := reflection_log_9008_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9009_neg : (136731 / 500000000) ≤ -Real.log (2000000 / 2000547) ∧
    -Real.log (2000000 / 2000547) ≤ (273463 / 1000000000) := by
  have h := checkLog_sound (w := (547 / 4000547)) (n := 12)
    (lo := (136731 / 500000000)) (hi := (273463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000547 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000547 / 2000000) = 1/(2000000 / 2000547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9009 : Bounds (136731 / 500000000) (273463 / 1000000000) (Real.log (2000547 / 2000000)) := by
  have h := reflection_log_9009_neg
  have he : Real.log (2000547 / 2000000) = -Real.log (2000000 / 2000547) := by
    rw [show ((2000547 / 2000000) : ℝ) = ((2000000 / 2000547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9010_neg : (273537 / 1000000000) ≤ -Real.log (1999453 / 2000000) ∧
    -Real.log (1999453 / 2000000) ≤ (136769 / 500000000) := by
  have h := checkLog_sound (w := (547 / 3999453)) (n := 12)
    (lo := (273537 / 1000000000)) (hi := (136769 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999453) = 1/(1999453 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9010 : Bounds (-136769 / 500000000) (-273537 / 1000000000) (Real.log (1999453 / 2000000)) := by
  have h := reflection_log_9010_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9011_neg : (16185511 / 125000000) ≤ -Real.log (1000000 / 1138241) ∧
    -Real.log (1000000 / 1138241) ≤ (129484089 / 1000000000) := by
  have h := checkLog_sound (w := (138241 / 2138241)) (n := 12)
    (lo := (16185511 / 125000000)) (hi := (129484089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1138241 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1138241 / 1000000) = 1/(1000000 / 1138241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9011 : Bounds (16185511 / 125000000) (129484089 / 1000000000) (Real.log (1138241 / 1000000)) := by
  have h := reflection_log_9011_neg
  have he : Real.log (1138241 / 1000000) = -Real.log (1000000 / 1138241) := by
    rw [show ((1138241 / 1000000) : ℝ) = ((1000000 / 1138241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9012_neg : (148779629 / 1000000000) ≤ -Real.log (861759 / 1000000) ∧
    -Real.log (861759 / 1000000) ≤ (14877963 / 100000000) := by
  have h := checkLog_sound (w := (138241 / 1861759)) (n := 12)
    (lo := (148779629 / 1000000000)) (hi := (14877963 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 861759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 861759) = 1/(861759 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9012 : Bounds (-14877963 / 100000000) (-148779629 / 1000000000) (Real.log (861759 / 1000000)) := by
  have h := reflection_log_9012_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9013_neg : (16243811 / 125000000) ≤ -Real.log (250000 / 284693) ∧
    -Real.log (250000 / 284693) ≤ (129950489 / 1000000000) := by
  have h := checkLog_sound (w := (34693 / 534693)) (n := 12)
    (lo := (16243811 / 125000000)) (hi := (129950489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((284693 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(284693 / 250000) = 1/(250000 / 284693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9013 : Bounds (16243811 / 125000000) (129950489 / 1000000000) (Real.log (284693 / 250000)) := by
  have h := reflection_log_9013_neg
  have he : Real.log (284693 / 250000) = -Real.log (250000 / 284693) := by
    rw [show ((284693 / 250000) : ℝ) = ((250000 / 284693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9014_neg : (149396001 / 1000000000) ≤ -Real.log (215307 / 250000) ∧
    -Real.log (215307 / 250000) ≤ (74698001 / 500000000) := by
  have h := checkLog_sound (w := (34693 / 465307)) (n := 12)
    (lo := (149396001 / 1000000000)) (hi := (74698001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 215307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 215307) = 1/(215307 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9014 : Bounds (-74698001 / 500000000) (-149396001 / 1000000000) (Real.log (215307 / 250000)) := by
  have h := reflection_log_9014_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9015_neg : (2430689 / 125000000) ≤ -Real.log (61296395751 / 62500000000) ∧
    -Real.log (61296395751 / 62500000000) ≤ (19445513 / 1000000000) := by
  have h := checkLog_sound (w := (1203604249 / 123796395751)) (n := 12)
    (lo := (2430689 / 125000000)) (hi := (19445513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61296395751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61296395751) = 1/(61296395751 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9015 : Bounds (-19445513 / 1000000000) (-2430689 / 125000000) (Real.log (61296395751 / 62500000000)) := by
  have h := reflection_log_9015_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9016_neg : (19295541 / 1000000000) ≤ -Real.log (980889425919 / 1000000000000) ∧
    -Real.log (980889425919 / 1000000000000) ≤ (9647771 / 500000000) := by
  have h := checkLog_sound (w := (19110574081 / 1980889425919)) (n := 12)
    (lo := (19295541 / 1000000000)) (hi := (9647771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980889425919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980889425919) = 1/(980889425919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9016 : Bounds (-9647771 / 500000000) (-19295541 / 1000000000) (Real.log (980889425919 / 1000000000000)) := by
  have h := reflection_log_9016_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9017_neg : (139131859 / 500000000) ≤ -Real.log (250000000000 / 330208619811) ∧
    -Real.log (250000000000 / 330208619811) ≤ (278263719 / 1000000000) := by
  have h := checkLog_sound (w := (80208619811 / 580208619811)) (n := 12)
    (lo := (139131859 / 500000000)) (hi := (278263719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330208619811 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(330208619811 / 250000000000) = 1/(250000000000 / 330208619811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9017 : Bounds (139131859 / 500000000) (278263719 / 1000000000) (Real.log (330208619811 / 250000000000)) := by
  have h := reflection_log_9017_neg
  have he : Real.log (330208619811 / 250000000000) = -Real.log (250000000000 / 330208619811) := by
    rw [show ((330208619811 / 250000000000) : ℝ) = ((250000000000 / 330208619811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9018_neg : (27934649 / 100000000) ≤ -Real.log (25000000000 / 33056635409) ∧
    -Real.log (25000000000 / 33056635409) ≤ (279346491 / 1000000000) := by
  have h := checkLog_sound (w := (8056635409 / 58056635409)) (n := 12)
    (lo := (27934649 / 100000000)) (hi := (279346491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33056635409 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33056635409 / 25000000000) = 1/(25000000000 / 33056635409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9018 : Bounds (27934649 / 100000000) (279346491 / 1000000000) (Real.log (33056635409 / 25000000000)) := by
  have h := reflection_log_9018_neg
  have he : Real.log (33056635409 / 25000000000) = -Real.log (25000000000 / 33056635409) := by
    rw [show ((33056635409 / 25000000000) : ℝ) = ((25000000000 / 33056635409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9019_neg : (560205121 / 1000000000) ≤ -Real.log (500000000000 / 875515818431) ∧
    -Real.log (500000000000 / 875515818431) ≤ (280102561 / 500000000) := by
  have h := checkLog_sound (w := (375515818431 / 1375515818431)) (n := 12)
    (lo := (560205121 / 1000000000)) (hi := (280102561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((875515818431 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(875515818431 / 500000000000) = 1/(500000000000 / 875515818431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9019 : Bounds (560205121 / 1000000000) (280102561 / 500000000) (Real.log (875515818431 / 500000000000)) := by
  have h := reflection_log_9019_neg
  have he : Real.log (875515818431 / 500000000000) = -Real.log (500000000000 / 875515818431) := by
    rw [show ((875515818431 / 500000000000) : ℝ) = ((500000000000 / 875515818431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9020_neg : (561285811 / 1000000000) ≤ -Real.log (250000000000 / 438231245699) ∧
    -Real.log (250000000000 / 438231245699) ≤ (140321453 / 250000000) := by
  have h := checkLog_sound (w := (188231245699 / 688231245699)) (n := 12)
    (lo := (561285811 / 1000000000)) (hi := (140321453 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((438231245699 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(438231245699 / 250000000000) = 1/(250000000000 / 438231245699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9020 : Bounds (561285811 / 1000000000) (140321453 / 250000000) (Real.log (438231245699 / 250000000000)) := by
  have h := reflection_log_9020_neg
  have he : Real.log (438231245699 / 250000000000) = -Real.log (250000000000 / 438231245699) := by
    rw [show ((438231245699 / 250000000000) : ℝ) = ((250000000000 / 438231245699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9021_neg : (242161557 / 1000000000) ≤ -Real.log (500 / 637) ∧
    -Real.log (500 / 637) ≤ (121080779 / 500000000) := by
  have h := checkLog_sound (w := (137 / 1137)) (n := 12)
    (lo := (242161557 / 1000000000)) (hi := (121080779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((637 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(637 / 500) = 1/(500 / 637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9021 : Bounds (242161557 / 1000000000) (121080779 / 500000000) (Real.log (637 / 500)) := by
  have h := reflection_log_9021_neg
  have he : Real.log (637 / 500) = -Real.log (500 / 637) := by
    rw [show ((637 / 500) : ℝ) = ((500 / 637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_9022_neg : (20012829 / 62500000) ≤ -Real.log (363 / 500) ∧
    -Real.log (363 / 500) ≤ (64041053 / 200000000) := by
  have h := checkLog_sound (w := (137 / 863)) (n := 12)
    (lo := (20012829 / 62500000)) (hi := (64041053 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 363) = 1/(363 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9022 : Bounds (-64041053 / 200000000) (-20012829 / 62500000) (Real.log (363 / 500)) := by
  have h := reflection_log_9022_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9023_neg : (136981 / 500000000) ≤ -Real.log (500000 / 500137) ∧
    -Real.log (500000 / 500137) ≤ (273963 / 1000000000) := by
  have h := checkLog_sound (w := (137 / 1000137)) (n := 12)
    (lo := (136981 / 500000000)) (hi := (273963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500137 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500137 / 500000) = 1/(500000 / 500137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9023 : Bounds (136981 / 500000000) (273963 / 1000000000) (Real.log (500137 / 500000)) := by
  have h := reflection_log_9023_neg
  have he : Real.log (500137 / 500000) = -Real.log (500000 / 500137) := by
    rw [show ((500137 / 500000) : ℝ) = ((500000 / 500137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
