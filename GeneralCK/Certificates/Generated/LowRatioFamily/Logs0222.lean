import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14208_neg : (408772299 / 1000000000) ≤ -Real.log (1000000 / 1504969) ∧
    -Real.log (1000000 / 1504969) ≤ (4087723 / 10000000) := by
  have h := checkLog_sound (w := (504969 / 2504969)) (n := 12)
    (lo := (408772299 / 1000000000)) (hi := (4087723 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1504969 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1504969 / 1000000) = 1/(1000000 / 1504969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14208 : Bounds (408772299 / 1000000000) (4087723 / 10000000) (Real.log (1504969 / 1000000)) := by
  have h := reflection_log_14208_neg
  have he : Real.log (1504969 / 1000000) = -Real.log (1000000 / 1504969) := by
    rw [show ((1504969 / 1000000) : ℝ) = ((1000000 / 1504969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14209_neg : (703134891 / 1000000000) ≤ -Real.log (495031 / 1000000) ∧
    -Real.log (495031 / 1000000) ≤ (703134893 / 1000000000) := by
  have h := checkLog_sound (w := (4969 / 995031)) (n := 12)
    (lo := (9987711 / 1000000000)) (hi := (78029 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 495031) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 495031) = 1/(495031 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14209 : Bounds (-703134893 / 1000000000) (-703134891 / 1000000000) (Real.log (495031 / 1000000)) := by
  have h := reflection_log_14209_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14210_neg : (9198831 / 31250000) ≤ -Real.log (745006309039 / 1000000000000) ∧
    -Real.log (745006309039 / 1000000000000) ≤ (294362593 / 1000000000) := by
  have h := checkLog_sound (w := (254993690961 / 1745006309039)) (n := 12)
    (lo := (9198831 / 31250000)) (hi := (294362593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 745006309039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 745006309039) = 1/(745006309039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14210 : Bounds (-294362593 / 1000000000) (-9198831 / 31250000) (Real.log (745006309039 / 1000000000000)) := by
  have h := reflection_log_14210_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14211_neg : (145021171 / 500000000) ≤ -Real.log (29929275391 / 40000000000) ∧
    -Real.log (29929275391 / 40000000000) ≤ (290042343 / 1000000000) := by
  have h := checkLog_sound (w := (10070724609 / 69929275391)) (n := 12)
    (lo := (145021171 / 500000000)) (hi := (290042343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 29929275391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 29929275391) = 1/(29929275391 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14211 : Bounds (-290042343 / 1000000000) (-145021171 / 500000000) (Real.log (29929275391 / 40000000000)) := by
  have h := reflection_log_14211_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14212_neg : (275831127 / 250000000) ≤ -Real.log (100000000000 / 301417002017) ∧
    -Real.log (100000000000 / 301417002017) ≤ (110332451 / 100000000) := by
  have h := checkLog_sound (w := (101417002017 / 501417002017)) (n := 12)
    (lo := (25636083 / 62500000)) (hi := (410177329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301417002017 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(301417002017 / 200000000000) = 1/(100000000000 / 301417002017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14212 : Bounds (275831127 / 250000000) (110332451 / 100000000) (Real.log (301417002017 / 100000000000)) := by
  have h := reflection_log_14212_neg
  have he : Real.log (301417002017 / 100000000000) = -Real.log (100000000000 / 301417002017) := by
    rw [show ((301417002017 / 100000000000) : ℝ) = ((100000000000 / 301417002017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14213_neg : (1111907191 / 1000000000) ≤ -Real.log (500000000000 / 1520075510423) ∧
    -Real.log (500000000000 / 1520075510423) ≤ (1111907193 / 1000000000) := by
  have h := checkLog_sound (w := (520075510423 / 2520075510423)) (n := 12)
    (lo := (418760011 / 1000000000)) (hi := (104690003 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1520075510423 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1520075510423 / 1000000000000) = 1/(500000000000 / 1520075510423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14213 : Bounds (1111907191 / 1000000000) (1111907193 / 1000000000) (Real.log (1520075510423 / 500000000000)) := by
  have h := reflection_log_14213_neg
  have he : Real.log (1520075510423 / 500000000000) = -Real.log (500000000000 / 1520075510423) := by
    rw [show ((1520075510423 / 500000000000) : ℝ) = ((500000000000 / 1520075510423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14214_neg : (1270747061 / 500000000) ≤ -Real.log (500000000000 / 6349315068493) ∧
    -Real.log (500000000000 / 6349315068493) ≤ (1270747063 / 500000000) := by
  have h := checkLog_sound (w := (2349315068493 / 10349315068493)) (n := 12)
    (lo := (231026291 / 500000000)) (hi := (462052583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6349315068493 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6349315068493 / 4000000000000) = 1/(500000000000 / 6349315068493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14214 : Bounds (1270747061 / 500000000) (1270747063 / 500000000) (Real.log (6349315068493 / 500000000000)) := by
  have h := reflection_log_14214_neg
  have he : Real.log (6349315068493 / 500000000000) = -Real.log (500000000000 / 6349315068493) := by
    rw [show ((6349315068493 / 500000000000) : ℝ) = ((500000000000 / 6349315068493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14215_neg : (2563872929 / 1000000000) ≤ -Real.log (500000000000 / 6493006993007) ∧
    -Real.log (500000000000 / 6493006993007) ≤ (2563872933 / 1000000000) := by
  have h := checkLog_sound (w := (2493006993007 / 10493006993007)) (n := 12)
    (lo := (484431389 / 1000000000)) (hi := (48443139 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6493006993007 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6493006993007 / 4000000000000) = 1/(500000000000 / 6493006993007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14215 : Bounds (2563872929 / 1000000000) (2563872933 / 1000000000) (Real.log (6493006993007 / 500000000000)) := by
  have h := reflection_log_14215_neg
  have he : Real.log (6493006993007 / 500000000000) = -Real.log (500000000000 / 6493006993007) := by
    rw [show ((6493006993007 / 500000000000) : ℝ) = ((500000000000 / 6493006993007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14216_neg : (620576487 / 1000000000) ≤ -Real.log (50 / 93) ∧
    -Real.log (50 / 93) ≤ (77572061 / 125000000) := by
  have h := checkLog_sound (w := (43 / 143)) (n := 12)
    (lo := (620576487 / 1000000000)) (hi := (77572061 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93 / 50) = 1/(50 / 93) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14216 : Bounds (620576487 / 1000000000) (77572061 / 125000000) (Real.log (93 / 50)) := by
  have h := reflection_log_14216_neg
  have he : Real.log (93 / 50) = -Real.log (50 / 93) := by
    rw [show ((93 / 50) : ℝ) = ((50 / 93) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14217_neg : (393222571 / 200000000) ≤ -Real.log (7 / 50) ∧
    -Real.log (7 / 50) ≤ (983056429 / 500000000) := by
  have h := checkLog_sound (w := (11 / 39)) (n := 12)
    (lo := (115963699 / 200000000)) (hi := (1132458 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 14) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(25 / 14) = 1/(7 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14217 : Bounds (-983056429 / 500000000) (-393222571 / 200000000) (Real.log (7 / 50)) := by
  have h := reflection_log_14217_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14218_neg : (85963 / 100000000) ≤ -Real.log (50000 / 50043) ∧
    -Real.log (50000 / 50043) ≤ (859631 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 100043)) (n := 12)
    (lo := (85963 / 100000000)) (hi := (859631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50043 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50043 / 50000) = 1/(50000 / 50043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14218 : Bounds (85963 / 100000000) (859631 / 1000000000) (Real.log (50043 / 50000)) := by
  have h := reflection_log_14218_neg
  have he : Real.log (50043 / 50000) = -Real.log (50000 / 50043) := by
    rw [show ((50043 / 50000) : ℝ) = ((50000 / 50043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14219_neg : (86037 / 100000000) ≤ -Real.log (49957 / 50000) ∧
    -Real.log (49957 / 50000) ≤ (860371 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 99957)) (n := 12)
    (lo := (86037 / 100000000)) (hi := (860371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 49957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 49957) = 1/(49957 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14219 : Bounds (-860371 / 1000000000) (-86037 / 100000000) (Real.log (49957 / 50000)) := by
  have h := reflection_log_14219_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14220_neg : (408324349 / 1000000000) ≤ -Real.log (200000 / 300859) ∧
    -Real.log (200000 / 300859) ≤ (8166487 / 20000000) := by
  have h := checkLog_sound (w := (100859 / 500859)) (n := 12)
    (lo := (408324349 / 1000000000)) (hi := (8166487 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300859 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300859 / 200000) = 1/(200000 / 300859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14220 : Bounds (408324349 / 1000000000) (8166487 / 20000000) (Real.log (300859 / 200000)) := by
  have h := reflection_log_14220_neg
  have he : Real.log (300859 / 200000) = -Real.log (200000 / 300859) := by
    rw [show ((300859 / 200000) : ℝ) = ((200000 / 300859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14221_neg : (350887143 / 500000000) ≤ -Real.log (99141 / 200000) ∧
    -Real.log (99141 / 200000) ≤ (43860893 / 62500000) := by
  have h := checkLog_sound (w := (859 / 199141)) (n := 12)
    (lo := (4313553 / 500000000)) (hi := (8627107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99141) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 99141) = 1/(99141 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14221 : Bounds (-43860893 / 62500000) (-350887143 / 500000000) (Real.log (99141 / 200000)) := by
  have h := reflection_log_14221_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14222_neg : (25653871 / 62500000) ≤ -Real.log (500000 / 753757) ∧
    -Real.log (500000 / 753757) ≤ (410461937 / 1000000000) := by
  have h := checkLog_sound (w := (253757 / 1253757)) (n := 12)
    (lo := (25653871 / 62500000)) (hi := (410461937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((753757 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(753757 / 500000) = 1/(500000 / 753757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14222 : Bounds (25653871 / 62500000) (410461937 / 1000000000) (Real.log (753757 / 500000)) := by
  have h := reflection_log_14222_neg
  have he : Real.log (753757 / 500000) = -Real.log (500000 / 753757) := by
    rw [show ((753757 / 500000) : ℝ) = ((500000 / 753757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14223_neg : (177072311 / 250000000) ≤ -Real.log (246243 / 500000) ∧
    -Real.log (246243 / 500000) ≤ (354144623 / 500000000) := by
  have h := checkLog_sound (w := (3757 / 496243)) (n := 12)
    (lo := (946379 / 62500000)) (hi := (3028413 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 246243) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 246243) = 1/(246243 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14223 : Bounds (-354144623 / 500000000) (-177072311 / 250000000) (Real.log (246243 / 500000)) := by
  have h := reflection_log_14223_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14224_neg : (74456827 / 250000000) ≤ -Real.log (185607384951 / 250000000000) ∧
    -Real.log (185607384951 / 250000000000) ≤ (297827309 / 1000000000) := by
  have h := checkLog_sound (w := (64392615049 / 435607384951)) (n := 12)
    (lo := (74456827 / 250000000)) (hi := (297827309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 185607384951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 185607384951) = 1/(185607384951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14224 : Bounds (-297827309 / 1000000000) (-74456827 / 250000000) (Real.log (185607384951 / 250000000000)) := by
  have h := reflection_log_14224_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14225_neg : (293449937 / 1000000000) ≤ -Real.log (29827462119 / 40000000000) ∧
    -Real.log (29827462119 / 40000000000) ≤ (146724969 / 500000000) := by
  have h := checkLog_sound (w := (10172537881 / 69827462119)) (n := 12)
    (lo := (293449937 / 1000000000)) (hi := (146724969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 29827462119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 29827462119) = 1/(29827462119 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14225 : Bounds (-146724969 / 500000000) (-293449937 / 1000000000) (Real.log (29827462119 / 40000000000)) := by
  have h := reflection_log_14225_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14226_neg : (277524659 / 250000000) ≤ -Real.log (500000000000 / 1517328854863) ∧
    -Real.log (500000000000 / 1517328854863) ≤ (555049319 / 500000000) := by
  have h := checkLog_sound (w := (517328854863 / 2517328854863)) (n := 12)
    (lo := (13029733 / 31250000)) (hi := (416951457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1517328854863 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1517328854863 / 1000000000000) = 1/(500000000000 / 1517328854863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14226 : Bounds (277524659 / 250000000) (555049319 / 500000000) (Real.log (1517328854863 / 500000000000)) := by
  have h := reflection_log_14226_neg
  have he : Real.log (1517328854863 / 500000000000) = -Real.log (500000000000 / 1517328854863) := by
    rw [show ((1517328854863 / 500000000000) : ℝ) = ((500000000000 / 1517328854863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14227_neg : (1118751181 / 1000000000) ≤ -Real.log (125000000000 / 382628643251) ∧
    -Real.log (125000000000 / 382628643251) ≤ (1118751183 / 1000000000) := by
  have h := checkLog_sound (w := (132628643251 / 632628643251)) (n := 12)
    (lo := (425604001 / 1000000000)) (hi := (212802001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((382628643251 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(382628643251 / 250000000000) = 1/(125000000000 / 382628643251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14227 : Bounds (1118751181 / 1000000000) (1118751183 / 1000000000) (Real.log (382628643251 / 125000000000)) := by
  have h := reflection_log_14227_neg
  have he : Real.log (382628643251 / 125000000000) = -Real.log (125000000000 / 382628643251) := by
    rw [show ((382628643251 / 125000000000) : ℝ) = ((125000000000 / 382628643251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14228_neg : (2563872929 / 1000000000) ≤ -Real.log (250000000000 / 3246503496503) ∧
    -Real.log (250000000000 / 3246503496503) ≤ (2563872933 / 1000000000) := by
  have h := checkLog_sound (w := (1246503496503 / 5246503496503)) (n := 12)
    (lo := (484431389 / 1000000000)) (hi := (48443139 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3246503496503 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3246503496503 / 2000000000000) = 1/(250000000000 / 3246503496503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14228 : Bounds (2563872929 / 1000000000) (2563872933 / 1000000000) (Real.log (3246503496503 / 250000000000)) := by
  have h := reflection_log_14228_neg
  have he : Real.log (3246503496503 / 250000000000) = -Real.log (250000000000 / 3246503496503) := by
    rw [show ((3246503496503 / 250000000000) : ℝ) = ((250000000000 / 3246503496503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14229_neg : (1293344671 / 500000000) ≤ -Real.log (250000000000 / 3321428571429) ∧
    -Real.log (250000000000 / 3321428571429) ≤ (1293344673 / 500000000) := by
  have h := checkLog_sound (w := (1321428571429 / 5321428571429)) (n := 12)
    (lo := (253623901 / 500000000)) (hi := (507247803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3321428571429 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3321428571429 / 2000000000000) = 1/(250000000000 / 3321428571429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14229 : Bounds (1293344671 / 500000000) (1293344673 / 500000000) (Real.log (3321428571429 / 250000000000)) := by
  have h := reflection_log_14229_neg
  have he : Real.log (3321428571429 / 250000000000) = -Real.log (250000000000 / 3321428571429) := by
    rw [show ((3321428571429 / 250000000000) : ℝ) = ((250000000000 / 3321428571429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14230_neg : (622188091 / 1000000000) ≤ -Real.log (1000 / 1863) ∧
    -Real.log (1000 / 1863) ≤ (155547023 / 250000000) := by
  have h := checkLog_sound (w := (863 / 2863)) (n := 12)
    (lo := (622188091 / 1000000000)) (hi := (155547023 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1863 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1863 / 1000) = 1/(1000 / 1863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14230 : Bounds (622188091 / 1000000000) (155547023 / 250000000) (Real.log (1863 / 1000)) := by
  have h := reflection_log_14230_neg
  have he : Real.log (1863 / 1000) = -Real.log (1000 / 1863) := by
    rw [show ((1863 / 1000) : ℝ) = ((1000 / 1863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14231_neg : (124235897 / 62500000) ≤ -Real.log (137 / 1000) ∧
    -Real.log (137 / 1000) ≤ (397554871 / 200000000) := by
  have h := checkLog_sound (w := (113 / 387)) (n := 12)
    (lo := (75184999 / 125000000)) (hi := (601479993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 137) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 137) = 1/(137 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14231 : Bounds (-397554871 / 200000000) (-124235897 / 62500000) (Real.log (137 / 1000)) := by
  have h := reflection_log_14231_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14232_neg : (862627 / 1000000000) ≤ -Real.log (1000000 / 1000863) ∧
    -Real.log (1000000 / 1000863) ≤ (215657 / 250000000) := by
  have h := checkLog_sound (w := (863 / 2000863)) (n := 12)
    (lo := (862627 / 1000000000)) (hi := (215657 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000863 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000863 / 1000000) = 1/(1000000 / 1000863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14232 : Bounds (862627 / 1000000000) (215657 / 250000000) (Real.log (1000863 / 1000000)) := by
  have h := reflection_log_14232_neg
  have he : Real.log (1000863 / 1000000) = -Real.log (1000000 / 1000863) := by
    rw [show ((1000863 / 1000000) : ℝ) = ((1000000 / 1000863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14233_neg : (215843 / 250000000) ≤ -Real.log (999137 / 1000000) ∧
    -Real.log (999137 / 1000000) ≤ (863373 / 1000000000) := by
  have h := checkLog_sound (w := (863 / 1999137)) (n := 12)
    (lo := (215843 / 250000000)) (hi := (863373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999137) = 1/(999137 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14233 : Bounds (-863373 / 1000000000) (-215843 / 250000000) (Real.log (999137 / 1000000)) := by
  have h := reflection_log_14233_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14234_neg : (205007371 / 500000000) ≤ -Real.log (25000 / 37671) ∧
    -Real.log (25000 / 37671) ≤ (410014743 / 1000000000) := by
  have h := checkLog_sound (w := (12671 / 62671)) (n := 12)
    (lo := (205007371 / 500000000)) (hi := (410014743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37671 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37671 / 25000) = 1/(25000 / 37671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14234 : Bounds (205007371 / 500000000) (410014743 / 1000000000) (Real.log (37671 / 25000)) := by
  have h := reflection_log_14234_neg
  have he : Real.log (37671 / 25000) = -Real.log (25000 / 37671) := by
    rw [show ((37671 / 25000) : ℝ) = ((25000 / 37671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14235_neg : (706921613 / 1000000000) ≤ -Real.log (12329 / 25000) ∧
    -Real.log (12329 / 25000) ≤ (141384323 / 200000000) := by
  have h := checkLog_sound (w := (171 / 24829)) (n := 12)
    (lo := (13774433 / 1000000000)) (hi := (6887217 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 12329) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(12500 / 12329) = 1/(12329 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14235 : Bounds (-141384323 / 200000000) (-706921613 / 1000000000) (Real.log (12329 / 25000)) := by
  have h := reflection_log_14235_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14236_neg : (6439979 / 15625000) ≤ -Real.log (500000 / 755037) ∧
    -Real.log (500000 / 755037) ≤ (412158657 / 1000000000) := by
  have h := checkLog_sound (w := (255037 / 1255037)) (n := 12)
    (lo := (6439979 / 15625000)) (hi := (412158657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((755037 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(755037 / 500000) = 1/(500000 / 755037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14236 : Bounds (6439979 / 15625000) (412158657 / 1000000000) (Real.log (755037 / 500000)) := by
  have h := reflection_log_14236_neg
  have he : Real.log (755037 / 500000) = -Real.log (500000 / 755037) := by
    rw [show ((755037 / 500000) : ℝ) = ((500000 / 755037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14237_neg : (713500919 / 1000000000) ≤ -Real.log (244963 / 500000) ∧
    -Real.log (244963 / 500000) ≤ (713500921 / 1000000000) := by
  have h := checkLog_sound (w := (5037 / 494963)) (n := 12)
    (lo := (20353739 / 1000000000)) (hi := (1017687 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 244963) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 244963) = 1/(244963 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14237 : Bounds (-713500921 / 1000000000) (-713500919 / 1000000000) (Real.log (244963 / 500000)) := by
  have h := reflection_log_14237_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14238_neg : (301342263 / 1000000000) ≤ -Real.log (184956128631 / 250000000000) ∧
    -Real.log (184956128631 / 250000000000) ≤ (37667783 / 125000000) := by
  have h := checkLog_sound (w := (65043871369 / 434956128631)) (n := 12)
    (lo := (301342263 / 1000000000)) (hi := (37667783 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 184956128631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 184956128631) = 1/(184956128631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14238 : Bounds (-37667783 / 125000000) (-301342263 / 1000000000) (Real.log (184956128631 / 250000000000)) := by
  have h := reflection_log_14238_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14239_neg : (296906871 / 1000000000) ≤ -Real.log (464445759 / 625000000) ∧
    -Real.log (464445759 / 625000000) ≤ (37113359 / 125000000) := by
  have h := checkLog_sound (w := (160554241 / 1089445759)) (n := 12)
    (lo := (296906871 / 1000000000)) (hi := (37113359 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 464445759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 464445759) = 1/(464445759 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14239 : Bounds (-37113359 / 125000000) (-296906871 / 1000000000) (Real.log (464445759 / 625000000)) := by
  have h := reflection_log_14239_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14240_neg : (279234089 / 250000000) ≤ -Real.log (7812500000 / 23870929313) ∧
    -Real.log (7812500000 / 23870929313) ≤ (558468179 / 500000000) := by
  have h := checkLog_sound (w := (8245929313 / 39495929313)) (n := 12)
    (lo := (52973647 / 125000000)) (hi := (423789177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23870929313 / 15625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(23870929313 / 15625000000) = 1/(7812500000 / 23870929313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14240 : Bounds (279234089 / 250000000) (558468179 / 500000000) (Real.log (23870929313 / 7812500000)) := by
  have h := reflection_log_14240_neg
  have he : Real.log (23870929313 / 7812500000) = -Real.log (7812500000 / 23870929313) := by
    rw [show ((23870929313 / 7812500000) : ℝ) = ((7812500000 / 23870929313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14241_neg : (45026383 / 40000000) ≤ -Real.log (250000000000 / 770562288999) ∧
    -Real.log (250000000000 / 770562288999) ≤ (1125659577 / 1000000000) := by
  have h := checkLog_sound (w := (270562288999 / 1270562288999)) (n := 12)
    (lo := (86502479 / 200000000)) (hi := (108128099 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((770562288999 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(770562288999 / 500000000000) = 1/(250000000000 / 770562288999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14241 : Bounds (45026383 / 40000000) (1125659577 / 1000000000) (Real.log (770562288999 / 250000000000)) := by
  have h := reflection_log_14241_neg
  have he : Real.log (770562288999 / 250000000000) = -Real.log (250000000000 / 770562288999) := by
    rw [show ((770562288999 / 250000000000) : ℝ) = ((250000000000 / 770562288999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14242_neg : (1293344671 / 500000000) ≤ -Real.log (500000000000 / 6642857142857) ∧
    -Real.log (500000000000 / 6642857142857) ≤ (1293344673 / 500000000) := by
  have h := checkLog_sound (w := (2642857142857 / 10642857142857)) (n := 12)
    (lo := (253623901 / 500000000)) (hi := (507247803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6642857142857 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6642857142857 / 4000000000000) = 1/(500000000000 / 6642857142857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14242 : Bounds (1293344671 / 500000000) (1293344673 / 500000000) (Real.log (6642857142857 / 500000000000)) := by
  have h := reflection_log_14242_neg
  have he : Real.log (6642857142857 / 500000000000) = -Real.log (500000000000 / 6642857142857) := by
    rw [show ((6642857142857 / 500000000000) : ℝ) = ((500000000000 / 6642857142857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14243_neg : (2609962443 / 1000000000) ≤ -Real.log (500000000000 / 6799270072993) ∧
    -Real.log (500000000000 / 6799270072993) ≤ (2609962447 / 1000000000) := by
  have h := checkLog_sound (w := (2799270072993 / 10799270072993)) (n := 12)
    (lo := (530520903 / 1000000000)) (hi := (66315113 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6799270072993 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6799270072993 / 4000000000000) = 1/(500000000000 / 6799270072993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14243 : Bounds (2609962443 / 1000000000) (2609962447 / 1000000000) (Real.log (6799270072993 / 500000000000)) := by
  have h := reflection_log_14243_neg
  have he : Real.log (6799270072993 / 500000000000) = -Real.log (500000000000 / 6799270072993) := by
    rw [show ((6799270072993 / 500000000000) : ℝ) = ((500000000000 / 6799270072993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14244_neg : (311898551 / 500000000) ≤ -Real.log (500 / 933) ∧
    -Real.log (500 / 933) ≤ (623797103 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 1433)) (n := 12)
    (lo := (311898551 / 500000000)) (hi := (623797103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((933 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(933 / 500) = 1/(500 / 933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14244 : Bounds (311898551 / 500000000) (623797103 / 1000000000) (Real.log (933 / 500)) := by
  have h := reflection_log_14244_neg
  have he : Real.log (933 / 500) = -Real.log (500 / 933) := by
    rw [show ((933 / 500) : ℝ) = ((500 / 933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14245_neg : (2009915477 / 1000000000) ≤ -Real.log (67 / 500) ∧
    -Real.log (67 / 500) ≤ (50247887 / 25000000) := by
  have h := checkLog_sound (w := (29 / 96)) (n := 12)
    (lo := (623621117 / 1000000000)) (hi := (311810559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 67) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 67) = 1/(67 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14245 : Bounds (-50247887 / 25000000) (-2009915477 / 1000000000) (Real.log (67 / 500)) := by
  have h := reflection_log_14245_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14246_neg : (277 / 320000) ≤ -Real.log (500000 / 500433) ∧
    -Real.log (500000 / 500433) ≤ (432813 / 500000000) := by
  have h := checkLog_sound (w := (433 / 1000433)) (n := 12)
    (lo := (277 / 320000)) (hi := (432813 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500433 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500433 / 500000) = 1/(500000 / 500433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14246 : Bounds (277 / 320000) (432813 / 500000000) (Real.log (500433 / 500000)) := by
  have h := reflection_log_14246_neg
  have he : Real.log (500433 / 500000) = -Real.log (500000 / 500433) := by
    rw [show ((500433 / 500000) : ℝ) = ((500000 / 500433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14247_neg : (6931 / 8000000) ≤ -Real.log (499567 / 500000) ∧
    -Real.log (499567 / 500000) ≤ (108297 / 125000000) := by
  have h := checkLog_sound (w := (433 / 999567)) (n := 12)
    (lo := (6931 / 8000000)) (hi := (108297 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499567) = 1/(499567 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14247 : Bounds (-108297 / 125000000) (-6931 / 8000000) (Real.log (499567 / 500000)) := by
  have h := reflection_log_14247_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14248_neg : (205855779 / 500000000) ≤ -Real.log (1000000 / 1509399) ∧
    -Real.log (1000000 / 1509399) ≤ (411711559 / 1000000000) := by
  have h := checkLog_sound (w := (509399 / 2509399)) (n := 12)
    (lo := (205855779 / 500000000)) (hi := (411711559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1509399 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1509399 / 1000000) = 1/(1000000 / 1509399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14248 : Bounds (205855779 / 500000000) (411711559 / 1000000000) (Real.log (1509399 / 1000000)) := by
  have h := reflection_log_14248_neg
  have he : Real.log (1509399 / 1000000) = -Real.log (1000000 / 1509399) := by
    rw [show ((1509399 / 1000000) : ℝ) = ((1000000 / 1509399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14249_neg : (178031027 / 250000000) ≤ -Real.log (490601 / 1000000) ∧
    -Real.log (490601 / 1000000) ≤ (71212411 / 100000000) := by
  have h := checkLog_sound (w := (9399 / 990601)) (n := 12)
    (lo := (593029 / 31250000)) (hi := (18976929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 490601) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 490601) = 1/(490601 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14249 : Bounds (-71212411 / 100000000) (-178031027 / 250000000) (Real.log (490601 / 1000000)) := by
  have h := reflection_log_14249_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14250_neg : (413861757 / 1000000000) ≤ -Real.log (125000 / 189081) ∧
    -Real.log (125000 / 189081) ≤ (206930879 / 500000000) := by
  have h := checkLog_sound (w := (64081 / 314081)) (n := 12)
    (lo := (413861757 / 1000000000)) (hi := (206930879 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((189081 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(189081 / 125000) = 1/(125000 / 189081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14250 : Bounds (413861757 / 1000000000) (206930879 / 500000000) (Real.log (189081 / 125000)) := by
  have h := reflection_log_14250_neg
  have he : Real.log (189081 / 125000) = -Real.log (125000 / 189081) := by
    rw [show ((189081 / 125000) : ℝ) = ((125000 / 189081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14251_neg : (718768623 / 1000000000) ≤ -Real.log (60919 / 125000) ∧
    -Real.log (60919 / 125000) ≤ (5750149 / 8000000) := by
  have h := checkLog_sound (w := (1581 / 123419)) (n := 12)
    (lo := (25621443 / 1000000000)) (hi := (6405361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 60919) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 60919) = 1/(60919 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14251 : Bounds (-5750149 / 8000000) (-718768623 / 1000000000) (Real.log (60919 / 125000)) := by
  have h := reflection_log_14251_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14252_neg : (304906867 / 1000000000) ≤ -Real.log (11518625439 / 15625000000) ∧
    -Real.log (11518625439 / 15625000000) ≤ (76226717 / 250000000) := by
  have h := checkLog_sound (w := (4106374561 / 27143625439)) (n := 12)
    (lo := (304906867 / 1000000000)) (hi := (76226717 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 11518625439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 11518625439) = 1/(11518625439 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14252 : Bounds (-76226717 / 250000000) (-304906867 / 1000000000) (Real.log (11518625439 / 15625000000)) := by
  have h := reflection_log_14252_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14253_neg : (6008251 / 20000000) ≤ -Real.log (740512658799 / 1000000000000) ∧
    -Real.log (740512658799 / 1000000000000) ≤ (300412551 / 1000000000) := by
  have h := checkLog_sound (w := (259487341201 / 1740512658799)) (n := 12)
    (lo := (6008251 / 20000000)) (hi := (300412551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 740512658799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 740512658799) = 1/(740512658799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14253 : Bounds (-300412551 / 1000000000) (-6008251 / 20000000) (Real.log (740512658799 / 1000000000000)) := by
  have h := reflection_log_14253_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14254_neg : (561917833 / 500000000) ≤ -Real.log (125000000000 / 384579067307) ∧
    -Real.log (125000000000 / 384579067307) ≤ (280958917 / 250000000) := by
  have h := checkLog_sound (w := (134579067307 / 634579067307)) (n := 12)
    (lo := (215344243 / 500000000)) (hi := (430688487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((384579067307 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(384579067307 / 250000000000) = 1/(125000000000 / 384579067307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14254 : Bounds (561917833 / 500000000) (280958917 / 250000000) (Real.log (384579067307 / 125000000000)) := by
  have h := reflection_log_14254_neg
  have he : Real.log (384579067307 / 125000000000) = -Real.log (125000000000 / 384579067307) := by
    rw [show ((384579067307 / 125000000000) : ℝ) = ((125000000000 / 384579067307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14255_neg : (1132630381 / 1000000000) ≤ -Real.log (31250000000 / 96994061787) ∧
    -Real.log (31250000000 / 96994061787) ≤ (1132630383 / 1000000000) := by
  have h := checkLog_sound (w := (34494061787 / 159494061787)) (n := 12)
    (lo := (439483201 / 1000000000)) (hi := (219741601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96994061787 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(96994061787 / 62500000000) = 1/(31250000000 / 96994061787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14255 : Bounds (1132630381 / 1000000000) (1132630383 / 1000000000) (Real.log (96994061787 / 31250000000)) := by
  have h := reflection_log_14255_neg
  have he : Real.log (96994061787 / 31250000000) = -Real.log (31250000000 / 96994061787) := by
    rw [show ((96994061787 / 31250000000) : ℝ) = ((31250000000 / 96994061787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14256_neg : (2609962443 / 1000000000) ≤ -Real.log (15625000000 / 212477189781) ∧
    -Real.log (15625000000 / 212477189781) ≤ (2609962447 / 1000000000) := by
  have h := checkLog_sound (w := (87477189781 / 337477189781)) (n := 12)
    (lo := (530520903 / 1000000000)) (hi := (66315113 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((212477189781 / 125000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(212477189781 / 125000000000) = 1/(15625000000 / 212477189781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14256 : Bounds (2609962443 / 1000000000) (2609962447 / 1000000000) (Real.log (212477189781 / 15625000000)) := by
  have h := reflection_log_14256_neg
  have he : Real.log (212477189781 / 15625000000) = -Real.log (15625000000 / 212477189781) := by
    rw [show ((212477189781 / 15625000000) : ℝ) = ((15625000000 / 212477189781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14257_neg : (2633712579 / 1000000000) ≤ -Real.log (100000000000 / 1392537313433) ∧
    -Real.log (100000000000 / 1392537313433) ≤ (2633712583 / 1000000000) := by
  have h := checkLog_sound (w := (592537313433 / 2192537313433)) (n := 12)
    (lo := (554271039 / 1000000000)) (hi := (1732097 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1392537313433 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1392537313433 / 800000000000) = 1/(100000000000 / 1392537313433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14257 : Bounds (2633712579 / 1000000000) (2633712583 / 1000000000) (Real.log (1392537313433 / 100000000000)) := by
  have h := reflection_log_14257_neg
  have he : Real.log (1392537313433 / 100000000000) = -Real.log (100000000000 / 1392537313433) := by
    rw [show ((1392537313433 / 100000000000) : ℝ) = ((100000000000 / 1392537313433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14258_neg : (78175441 / 125000000) ≤ -Real.log (1000 / 1869) ∧
    -Real.log (1000 / 1869) ≤ (625403529 / 1000000000) := by
  have h := checkLog_sound (w := (869 / 2869)) (n := 12)
    (lo := (78175441 / 125000000)) (hi := (625403529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1869 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1869 / 1000) = 1/(1000 / 1869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14258 : Bounds (78175441 / 125000000) (625403529 / 1000000000) (Real.log (1869 / 1000)) := by
  have h := reflection_log_14258_neg
  have he : Real.log (1869 / 1000) = -Real.log (1000 / 1869) := by
    rw [show ((1869 / 1000) : ℝ) = ((1000 / 1869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14259_neg : (1016278977 / 500000000) ≤ -Real.log (131 / 1000) ∧
    -Real.log (131 / 1000) ≤ (2032557957 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 381)) (n := 12)
    (lo := (323131797 / 500000000)) (hi := (129252719 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 131) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 131) = 1/(131 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14259 : Bounds (-2032557957 / 1000000000) (-1016278977 / 500000000) (Real.log (131 / 1000)) := by
  have h := reflection_log_14259_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14260_neg : (434311 / 500000000) ≤ -Real.log (1000000 / 1000869) ∧
    -Real.log (1000000 / 1000869) ≤ (868623 / 1000000000) := by
  have h := checkLog_sound (w := (869 / 2000869)) (n := 12)
    (lo := (434311 / 500000000)) (hi := (868623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000869 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000869 / 1000000) = 1/(1000000 / 1000869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14260 : Bounds (434311 / 500000000) (868623 / 1000000000) (Real.log (1000869 / 1000000)) := by
  have h := reflection_log_14260_neg
  have he : Real.log (1000869 / 1000000) = -Real.log (1000000 / 1000869) := by
    rw [show ((1000869 / 1000000) : ℝ) = ((1000000 / 1000869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14261_neg : (869377 / 1000000000) ≤ -Real.log (999131 / 1000000) ∧
    -Real.log (999131 / 1000000) ≤ (434689 / 500000000) := by
  have h := checkLog_sound (w := (869 / 1999131)) (n := 12)
    (lo := (869377 / 1000000000)) (hi := (434689 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999131) = 1/(999131 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14261 : Bounds (-434689 / 500000000) (-869377 / 1000000000) (Real.log (999131 / 1000000)) := by
  have h := reflection_log_14261_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14262_neg : (413416081 / 1000000000) ≤ -Real.log (500000 / 755987) ∧
    -Real.log (500000 / 755987) ≤ (206708041 / 500000000) := by
  have h := checkLog_sound (w := (255987 / 1255987)) (n := 12)
    (lo := (413416081 / 1000000000)) (hi := (206708041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((755987 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(755987 / 500000) = 1/(500000 / 755987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14262 : Bounds (413416081 / 1000000000) (206708041 / 500000000) (Real.log (755987 / 500000)) := by
  have h := reflection_log_14262_neg
  have he : Real.log (755987 / 500000) = -Real.log (500000 / 755987) := by
    rw [show ((755987 / 500000) : ℝ) = ((500000 / 755987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14263_neg : (143477319 / 200000000) ≤ -Real.log (244013 / 500000) ∧
    -Real.log (244013 / 500000) ≤ (717386597 / 1000000000) := by
  have h := checkLog_sound (w := (5987 / 494013)) (n := 12)
    (lo := (4847883 / 200000000)) (hi := (3029927 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 244013) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 244013) = 1/(244013 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14263 : Bounds (-717386597 / 1000000000) (-143477319 / 200000000) (Real.log (244013 / 500000)) := by
  have h := reflection_log_14263_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14264_neg : (207786591 / 500000000) ≤ -Real.log (1000000 / 1515239) ∧
    -Real.log (1000000 / 1515239) ≤ (415573183 / 1000000000) := by
  have h := checkLog_sound (w := (515239 / 2515239)) (n := 12)
    (lo := (207786591 / 500000000)) (hi := (415573183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1515239 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1515239 / 1000000) = 1/(1000000 / 1515239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14264 : Bounds (207786591 / 500000000) (415573183 / 1000000000) (Real.log (1515239 / 1000000)) := by
  have h := reflection_log_14264_neg
  have he : Real.log (1515239 / 1000000) = -Real.log (1000000 / 1515239) := by
    rw [show ((1515239 / 1000000) : ℝ) = ((1000000 / 1515239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14265_neg : (181024823 / 250000000) ≤ -Real.log (484761 / 1000000) ∧
    -Real.log (484761 / 1000000) ≤ (362049647 / 500000000) := by
  have h := checkLog_sound (w := (15239 / 984761)) (n := 12)
    (lo := (1934507 / 62500000)) (hi := (30952113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 484761) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 484761) = 1/(484761 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14265 : Bounds (-362049647 / 500000000) (-181024823 / 250000000) (Real.log (484761 / 1000000)) := by
  have h := reflection_log_14265_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14266_neg : (30852611 / 100000000) ≤ -Real.log (734528772879 / 1000000000000) ∧
    -Real.log (734528772879 / 1000000000000) ≤ (308526111 / 1000000000) := by
  have h := checkLog_sound (w := (265471227121 / 1734528772879)) (n := 12)
    (lo := (30852611 / 100000000)) (hi := (308526111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 734528772879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 734528772879) = 1/(734528772879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14266 : Bounds (-308526111 / 1000000000) (-30852611 / 100000000) (Real.log (734528772879 / 1000000000000)) := by
  have h := reflection_log_14266_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14267_neg : (151985257 / 500000000) ≤ -Real.log (184470655831 / 250000000000) ∧
    -Real.log (184470655831 / 250000000000) ≤ (60794103 / 200000000) := by
  have h := checkLog_sound (w := (65529344169 / 434470655831)) (n := 12)
    (lo := (151985257 / 500000000)) (hi := (60794103 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 184470655831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 184470655831) = 1/(184470655831 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14267 : Bounds (-60794103 / 200000000) (-151985257 / 500000000) (Real.log (184470655831 / 250000000000)) := by
  have h := reflection_log_14267_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14268_neg : (1130802677 / 1000000000) ≤ -Real.log (125000000000 / 387267789011) ∧
    -Real.log (125000000000 / 387267789011) ≤ (1130802679 / 1000000000) := by
  have h := checkLog_sound (w := (137267789011 / 637267789011)) (n := 12)
    (lo := (437655497 / 1000000000)) (hi := (218827749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387267789011 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(387267789011 / 250000000000) = 1/(125000000000 / 387267789011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14268 : Bounds (1130802677 / 1000000000) (1130802679 / 1000000000) (Real.log (387267789011 / 125000000000)) := by
  have h := reflection_log_14268_neg
  have he : Real.log (387267789011 / 125000000000) = -Real.log (125000000000 / 387267789011) := by
    rw [show ((387267789011 / 125000000000) : ℝ) = ((125000000000 / 387267789011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14269_neg : (569836237 / 500000000) ≤ -Real.log (500000000000 / 1562872219507) ∧
    -Real.log (500000000000 / 1562872219507) ≤ (284918119 / 250000000) := by
  have h := checkLog_sound (w := (562872219507 / 2562872219507)) (n := 12)
    (lo := (223262647 / 500000000)) (hi := (89305059 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1562872219507 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1562872219507 / 1000000000000) = 1/(500000000000 / 1562872219507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14269 : Bounds (569836237 / 500000000) (284918119 / 250000000) (Real.log (1562872219507 / 500000000000)) := by
  have h := reflection_log_14269_neg
  have he : Real.log (1562872219507 / 500000000000) = -Real.log (500000000000 / 1562872219507) := by
    rw [show ((1562872219507 / 500000000000) : ℝ) = ((500000000000 / 1562872219507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14270_neg : (2633712579 / 1000000000) ≤ -Real.log (125000000000 / 1740671641791) ∧
    -Real.log (125000000000 / 1740671641791) ≤ (2633712583 / 1000000000) := by
  have h := checkLog_sound (w := (740671641791 / 2740671641791)) (n := 12)
    (lo := (554271039 / 1000000000)) (hi := (1732097 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1740671641791 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1740671641791 / 1000000000000) = 1/(125000000000 / 1740671641791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14270 : Bounds (2633712579 / 1000000000) (2633712583 / 1000000000) (Real.log (1740671641791 / 125000000000)) := by
  have h := reflection_log_14270_neg
  have he : Real.log (1740671641791 / 125000000000) = -Real.log (125000000000 / 1740671641791) := by
    rw [show ((1740671641791 / 125000000000) : ℝ) = ((125000000000 / 1740671641791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14271_neg : (1328980741 / 500000000) ≤ -Real.log (25000000000 / 356679389313) ∧
    -Real.log (25000000000 / 356679389313) ≤ (1328980743 / 500000000) := by
  have h := checkLog_sound (w := (156679389313 / 556679389313)) (n := 12)
    (lo := (289259971 / 500000000)) (hi := (578519943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((356679389313 / 200000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(356679389313 / 200000000000) = 1/(25000000000 / 356679389313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14271 : Bounds (1328980741 / 500000000) (1328980743 / 500000000) (Real.log (356679389313 / 25000000000)) := by
  have h := reflection_log_14271_neg
  have he : Real.log (356679389313 / 25000000000) = -Real.log (25000000000 / 356679389313) := by
    rw [show ((356679389313 / 25000000000) : ℝ) = ((25000000000 / 356679389313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
