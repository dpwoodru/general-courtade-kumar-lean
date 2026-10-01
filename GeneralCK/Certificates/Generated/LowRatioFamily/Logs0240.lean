import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_15360_neg : (1038127911 / 1000000000) ≤ -Real.log (354117 / 1000000) ∧
    -Real.log (354117 / 1000000) ≤ (1038127913 / 1000000000) := by
  have h := checkLog_sound (w := (145883 / 854117)) (n := 12)
    (lo := (344980731 / 1000000000)) (hi := (86245183 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 354117) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 354117) = 1/(354117 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15360 : Bounds (-1038127913 / 1000000000) (-1038127911 / 1000000000) (Real.log (354117 / 1000000)) := by
  have h := reflection_log_15360_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15361_neg : (539850893 / 1000000000) ≤ -Real.log (582835150311 / 1000000000000) ∧
    -Real.log (582835150311 / 1000000000000) ≤ (269925447 / 500000000) := by
  have h := checkLog_sound (w := (417164849689 / 1582835150311)) (n := 12)
    (lo := (539850893 / 1000000000)) (hi := (269925447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 582835150311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 582835150311) = 1/(582835150311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15361 : Bounds (-269925447 / 500000000) (-539850893 / 1000000000) (Real.log (582835150311 / 1000000000000)) := by
  have h := reflection_log_15361_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15362_neg : (107557333 / 200000000) ≤ -Real.log (233615799 / 400000000) ∧
    -Real.log (233615799 / 400000000) ≤ (268893333 / 500000000) := by
  have h := checkLog_sound (w := (166384201 / 633615799)) (n := 12)
    (lo := (107557333 / 200000000)) (hi := (268893333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 233615799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 233615799) = 1/(233615799 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15362 : Bounds (-268893333 / 500000000) (-107557333 / 200000000) (Real.log (233615799 / 400000000)) := by
  have h := reflection_log_15362_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15363_neg : (1533206641 / 1000000000) ≤ -Real.log (100000000000 / 463300943529) ∧
    -Real.log (100000000000 / 463300943529) ≤ (383301661 / 250000000) := by
  have h := checkLog_sound (w := (63300943529 / 863300943529)) (n := 12)
    (lo := (146912281 / 1000000000)) (hi := (73456141 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((463300943529 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(463300943529 / 400000000000) = 1/(100000000000 / 463300943529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15363 : Bounds (1533206641 / 1000000000) (383301661 / 250000000) (Real.log (463300943529 / 100000000000)) := by
  have h := reflection_log_15363_neg
  have he : Real.log (463300943529 / 100000000000) = -Real.log (100000000000 / 463300943529) := by
    rw [show ((463300943529 / 100000000000) : ℝ) = ((100000000000 / 463300943529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15364_neg : (1536404929 / 1000000000) ≤ -Real.log (250000000000 / 1161962712889) ∧
    -Real.log (250000000000 / 1161962712889) ≤ (384101233 / 250000000) := by
  have h := checkLog_sound (w := (161962712889 / 2161962712889)) (n := 12)
    (lo := (150110569 / 1000000000)) (hi := (15011057 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1161962712889 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1161962712889 / 1000000000000) = 1/(250000000000 / 1161962712889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15364 : Bounds (1536404929 / 1000000000) (384101233 / 250000000) (Real.log (1161962712889 / 250000000000)) := by
  have h := reflection_log_15364_neg
  have he : Real.log (1161962712889 / 250000000000) = -Real.log (250000000000 / 1161962712889) := by
    rw [show ((1161962712889 / 250000000000) : ℝ) = ((250000000000 / 1161962712889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15365_neg : (5542871097 / 1000000000) ≤ -Real.log (62500000000 / 15963141025641) ∧
    -Real.log (62500000000 / 15963141025641) ≤ (1108574221 / 200000000) := by
  have h := checkLog_sound (w := (7963141025641 / 23963141025641)) (n := 12)
    (lo := (690840837 / 1000000000)) (hi := (345420419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15963141025641 / 8000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(15963141025641 / 8000000000000) = 1/(62500000000 / 15963141025641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15365 : Bounds (5542871097 / 1000000000) (1108574221 / 200000000) (Real.log (15963141025641 / 62500000000)) := by
  have h := reflection_log_15365_neg
  have he : Real.log (15963141025641 / 62500000000) = -Real.log (62500000000 / 15963141025641) := by
    rw [show ((15963141025641 / 62500000000) : ℝ) = ((62500000000 / 15963141025641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15366_neg : (5568946969 / 1000000000) ≤ -Real.log (250000000000 / 65539473684211) ∧
    -Real.log (250000000000 / 65539473684211) ≤ (2784473489 / 500000000) := by
  have h := checkLog_sound (w := (1539473684211 / 129539473684211)) (n := 12)
    (lo := (23769529 / 1000000000)) (hi := (2376953 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65539473684211 / 64000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(65539473684211 / 64000000000000) = 1/(250000000000 / 65539473684211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15366 : Bounds (5568946969 / 1000000000) (2784473489 / 500000000) (Real.log (65539473684211 / 250000000000)) := by
  have h := reflection_log_15366_neg
  have he : Real.log (65539473684211 / 250000000000) = -Real.log (250000000000 / 65539473684211) := by
    rw [show ((65539473684211 / 250000000000) : ℝ) = ((250000000000 / 65539473684211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15367_neg : (344720159 / 500000000) ≤ -Real.log (5000 / 9963) ∧
    -Real.log (5000 / 9963) ≤ (689440319 / 1000000000) := by
  have h := checkLog_sound (w := (4963 / 14963)) (n := 12)
    (lo := (344720159 / 500000000)) (hi := (689440319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9963 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9963 / 5000) = 1/(5000 / 9963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15367 : Bounds (344720159 / 500000000) (689440319 / 1000000000) (Real.log (9963 / 5000)) := by
  have h := reflection_log_15367_neg
  have he : Real.log (9963 / 5000) = -Real.log (5000 / 9963) := by
    rw [show ((9963 / 5000) : ℝ) = ((5000 / 9963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15368_neg : (2453137637 / 500000000) ≤ -Real.log (37 / 5000) ∧
    -Real.log (37 / 5000) ≤ (2453137641 / 500000000) := by
  have h := checkLog_sound (w := (33 / 1217)) (n := 12)
    (lo := (27122507 / 500000000)) (hi := (10849003 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 592) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 592) = 1/(37 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15368 : Bounds (-2453137641 / 500000000) (-2453137637 / 500000000) (Real.log (37 / 5000)) := by
  have h := reflection_log_15368_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15369_neg : (992107 / 1000000000) ≤ -Real.log (5000000 / 5004963) ∧
    -Real.log (5000000 / 5004963) ≤ (248027 / 250000000) := by
  have h := checkLog_sound (w := (4963 / 10004963)) (n := 12)
    (lo := (992107 / 1000000000)) (hi := (248027 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004963 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004963 / 5000000) = 1/(5000000 / 5004963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15369 : Bounds (992107 / 1000000000) (248027 / 250000000) (Real.log (5004963 / 5000000)) := by
  have h := reflection_log_15369_neg
  have he : Real.log (5004963 / 5000000) = -Real.log (5000000 / 5004963) := by
    rw [show ((5004963 / 5000000) : ℝ) = ((5000000 / 5004963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15370_neg : (248273 / 250000000) ≤ -Real.log (4995037 / 5000000) ∧
    -Real.log (4995037 / 5000000) ≤ (993093 / 1000000000) := by
  have h := checkLog_sound (w := (4963 / 9995037)) (n := 12)
    (lo := (248273 / 250000000)) (hi := (993093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995037) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995037) = 1/(4995037 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15370 : Bounds (-993093 / 1000000000) (-248273 / 250000000) (Real.log (4995037 / 5000000)) := by
  have h := reflection_log_15370_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15371_neg : (99579199 / 200000000) ≤ -Real.log (125000 / 205657) ∧
    -Real.log (125000 / 205657) ≤ (124473999 / 250000000) := by
  have h := checkLog_sound (w := (80657 / 330657)) (n := 12)
    (lo := (99579199 / 200000000)) (hi := (124473999 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((205657 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(205657 / 125000) = 1/(125000 / 205657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15371 : Bounds (99579199 / 200000000) (124473999 / 250000000) (Real.log (205657 / 125000)) := by
  have h := reflection_log_15371_neg
  have he : Real.log (205657 / 125000) = -Real.log (125000 / 205657) := by
    rw [show ((205657 / 125000) : ℝ) = ((125000 / 205657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15372_neg : (8290871 / 8000000) ≤ -Real.log (44343 / 125000) ∧
    -Real.log (44343 / 125000) ≤ (1036358877 / 1000000000) := by
  have h := checkLog_sound (w := (18157 / 106843)) (n := 12)
    (lo := (68642339 / 200000000)) (hi := (21450731 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44343) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 44343) = 1/(44343 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15372 : Bounds (-1036358877 / 1000000000) (-8290871 / 8000000) (Real.log (44343 / 125000)) := by
  have h := reflection_log_15372_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15373_neg : (249231763 / 500000000) ≤ -Real.log (100000 / 164619) ∧
    -Real.log (100000 / 164619) ≤ (498463527 / 1000000000) := by
  have h := checkLog_sound (w := (64619 / 264619)) (n := 12)
    (lo := (249231763 / 500000000)) (hi := (498463527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164619 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164619 / 100000) = 1/(100000 / 164619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15373 : Bounds (249231763 / 500000000) (498463527 / 1000000000) (Real.log (164619 / 100000)) := by
  have h := reflection_log_15373_neg
  have he : Real.log (164619 / 100000) = -Real.log (100000 / 164619) := by
    rw [show ((164619 / 100000) : ℝ) = ((100000 / 164619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15374_neg : (32468601 / 31250000) ≤ -Real.log (35381 / 100000) ∧
    -Real.log (35381 / 100000) ≤ (519497617 / 500000000) := by
  have h := checkLog_sound (w := (14619 / 85381)) (n := 12)
    (lo := (86462013 / 250000000)) (hi := (345848053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35381) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 35381) = 1/(35381 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15374 : Bounds (-519497617 / 500000000) (-32468601 / 31250000) (Real.log (35381 / 100000)) := by
  have h := reflection_log_15374_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15375_neg : (270265853 / 500000000) ≤ -Real.log (5824384839 / 10000000000) ∧
    -Real.log (5824384839 / 10000000000) ≤ (540531707 / 1000000000) := by
  have h := checkLog_sound (w := (4175615161 / 15824384839)) (n := 12)
    (lo := (270265853 / 500000000)) (hi := (540531707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 5824384839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 5824384839) = 1/(5824384839 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15375 : Bounds (-540531707 / 1000000000) (-270265853 / 500000000) (Real.log (5824384839 / 10000000000)) := by
  have h := reflection_log_15375_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15376_neg : (538462881 / 1000000000) ≤ -Real.log (9119448351 / 15625000000) ∧
    -Real.log (9119448351 / 15625000000) ≤ (269231441 / 500000000) := by
  have h := checkLog_sound (w := (6505551649 / 24744448351)) (n := 12)
    (lo := (538462881 / 1000000000)) (hi := (269231441 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 9119448351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 9119448351) = 1/(9119448351 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15376 : Bounds (-269231441 / 500000000) (-538462881 / 1000000000) (Real.log (9119448351 / 15625000000)) := by
  have h := reflection_log_15376_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15377_neg : (153425487 / 100000000) ≤ -Real.log (500000000000 / 2318934217351) ∧
    -Real.log (500000000000 / 2318934217351) ≤ (1534254873 / 1000000000) := by
  have h := checkLog_sound (w := (318934217351 / 4318934217351)) (n := 12)
    (lo := (14796051 / 100000000)) (hi := (147960511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2318934217351 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2318934217351 / 2000000000000) = 1/(500000000000 / 2318934217351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15377 : Bounds (153425487 / 100000000) (1534254873 / 1000000000) (Real.log (2318934217351 / 500000000000)) := by
  have h := reflection_log_15377_neg
  have he : Real.log (2318934217351 / 500000000000) = -Real.log (500000000000 / 2318934217351) := by
    rw [show ((2318934217351 / 500000000000) : ℝ) = ((500000000000 / 2318934217351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15378_neg : (768729379 / 500000000) ≤ -Real.log (500000000000 / 2326375738391) ∧
    -Real.log (500000000000 / 2326375738391) ≤ (1537458761 / 1000000000) := by
  have h := checkLog_sound (w := (326375738391 / 4326375738391)) (n := 12)
    (lo := (75582199 / 500000000)) (hi := (151164399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2326375738391 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2326375738391 / 2000000000000) = 1/(500000000000 / 2326375738391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15378 : Bounds (768729379 / 500000000) (1537458761 / 1000000000) (Real.log (2326375738391 / 500000000000)) := by
  have h := reflection_log_15378_neg
  have he : Real.log (2326375738391 / 500000000000) = -Real.log (500000000000 / 2326375738391) := by
    rw [show ((2326375738391 / 500000000000) : ℝ) = ((500000000000 / 2326375738391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15379_neg : (5568946969 / 1000000000) ≤ -Real.log (500000000000 / 131078947368421) ∧
    -Real.log (500000000000 / 131078947368421) ≤ (2784473489 / 500000000) := by
  have h := checkLog_sound (w := (3078947368421 / 259078947368421)) (n := 12)
    (lo := (23769529 / 1000000000)) (hi := (2376953 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((131078947368421 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(131078947368421 / 128000000000000) = 1/(500000000000 / 131078947368421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15379 : Bounds (5568946969 / 1000000000) (2784473489 / 500000000) (Real.log (131078947368421 / 500000000000)) := by
  have h := reflection_log_15379_neg
  have he : Real.log (131078947368421 / 500000000000) = -Real.log (500000000000 / 131078947368421) := by
    rw [show ((131078947368421 / 500000000000) : ℝ) = ((500000000000 / 131078947368421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15380_neg : (699464449 / 125000000) ≤ -Real.log (15625000000 / 4207347972973) ∧
    -Real.log (15625000000 / 4207347972973) ≤ (5595715601 / 1000000000) := by
  have h := checkLog_sound (w := (207347972973 / 8207347972973)) (n := 12)
    (lo := (6317269 / 125000000)) (hi := (50538153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4207347972973 / 4000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(4207347972973 / 4000000000000) = 1/(15625000000 / 4207347972973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15380 : Bounds (699464449 / 125000000) (5595715601 / 1000000000) (Real.log (4207347972973 / 15625000000)) := by
  have h := reflection_log_15380_neg
  have he : Real.log (4207347972973 / 15625000000) = -Real.log (15625000000 / 4207347972973) := by
    rw [show ((4207347972973 / 15625000000) : ℝ) = ((15625000000 / 4207347972973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15381_neg : (172385171 / 250000000) ≤ -Real.log (1250 / 2491) ∧
    -Real.log (1250 / 2491) ≤ (137908137 / 200000000) := by
  have h := checkLog_sound (w := (1241 / 3741)) (n := 12)
    (lo := (172385171 / 250000000)) (hi := (137908137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2491 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2491 / 1250) = 1/(1250 / 2491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15381 : Bounds (172385171 / 250000000) (137908137 / 200000000) (Real.log (2491 / 1250)) := by
  have h := reflection_log_15381_neg
  have he : Real.log (2491 / 1250) = -Real.log (1250 / 2491) := by
    rw [show ((2491 / 1250) : ℝ) = ((1250 / 2491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15382_neg : (4933674249 / 1000000000) ≤ -Real.log (9 / 1250) ∧
    -Real.log (9 / 1250) ≤ (4933674257 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 1201)) (n := 12)
    (lo := (81643989 / 1000000000)) (hi := (8164399 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 576) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 576) = 1/(9 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15382 : Bounds (-4933674257 / 1000000000) (-4933674249 / 1000000000) (Real.log (9 / 1250)) := by
  have h := reflection_log_15382_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15383_neg : (992307 / 1000000000) ≤ -Real.log (1250000 / 1251241) ∧
    -Real.log (1250000 / 1251241) ≤ (248077 / 250000000) := by
  have h := checkLog_sound (w := (1241 / 2501241)) (n := 12)
    (lo := (992307 / 1000000000)) (hi := (248077 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251241 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251241 / 1250000) = 1/(1250000 / 1251241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15383 : Bounds (992307 / 1000000000) (248077 / 250000000) (Real.log (1251241 / 1250000)) := by
  have h := reflection_log_15383_neg
  have he : Real.log (1251241 / 1250000) = -Real.log (1250000 / 1251241) := by
    rw [show ((1251241 / 1250000) : ℝ) = ((1250000 / 1251241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15384_neg : (993293 / 1000000000) ≤ -Real.log (1248759 / 1250000) ∧
    -Real.log (1248759 / 1250000) ≤ (496647 / 500000000) := by
  have h := checkLog_sound (w := (1241 / 2498759)) (n := 12)
    (lo := (993293 / 1000000000)) (hi := (496647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1248759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1248759) = 1/(1248759 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15384 : Bounds (-496647 / 500000000) (-993293 / 1000000000) (Real.log (1248759 / 1250000)) := by
  have h := reflection_log_15384_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15385_neg : (498081967 / 1000000000) ≤ -Real.log (500000 / 822781) ∧
    -Real.log (500000 / 822781) ≤ (31130123 / 62500000) := by
  have h := checkLog_sound (w := (322781 / 1322781)) (n := 12)
    (lo := (498081967 / 1000000000)) (hi := (31130123 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((822781 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(822781 / 500000) = 1/(500000 / 822781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15385 : Bounds (498081967 / 1000000000) (31130123 / 62500000) (Real.log (822781 / 500000)) := by
  have h := reflection_log_15385_neg
  have he : Real.log (822781 / 500000) = -Real.log (500000 / 822781) := by
    rw [show ((822781 / 500000) : ℝ) = ((500000 / 822781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15386_neg : (1037221841 / 1000000000) ≤ -Real.log (177219 / 500000) ∧
    -Real.log (177219 / 500000) ≤ (1037221843 / 1000000000) := by
  have h := checkLog_sound (w := (72781 / 427219)) (n := 12)
    (lo := (344074661 / 1000000000)) (hi := (172037331 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 177219) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 177219) = 1/(177219 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15386 : Bounds (-1037221843 / 1000000000) (-1037221841 / 1000000000) (Real.log (177219 / 500000)) := by
  have h := reflection_log_15386_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15387_neg : (31165663 / 62500000) ≤ -Real.log (500000 / 823249) ∧
    -Real.log (500000 / 823249) ≤ (498650609 / 1000000000) := by
  have h := checkLog_sound (w := (323249 / 1323249)) (n := 12)
    (lo := (31165663 / 62500000)) (hi := (498650609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((823249 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(823249 / 500000) = 1/(500000 / 823249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15387 : Bounds (31165663 / 62500000) (498650609 / 1000000000) (Real.log (823249 / 500000)) := by
  have h := reflection_log_15387_neg
  have he : Real.log (823249 / 500000) = -Real.log (500000 / 823249) := by
    rw [show ((823249 / 500000) : ℝ) = ((500000 / 823249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15388_neg : (207973227 / 200000000) ≤ -Real.log (176751 / 500000) ∧
    -Real.log (176751 / 500000) ≤ (1039866137 / 1000000000) := by
  have h := checkLog_sound (w := (73249 / 426751)) (n := 12)
    (lo := (69343791 / 200000000)) (hi := (86679739 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 176751) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 176751) = 1/(176751 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15388 : Bounds (-1039866137 / 1000000000) (-207973227 / 200000000) (Real.log (176751 / 500000)) := by
  have h := reflection_log_15388_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15389_neg : (541215527 / 1000000000) ≤ -Real.log (145510083999 / 250000000000) ∧
    -Real.log (145510083999 / 250000000000) ≤ (67651941 / 125000000) := by
  have h := checkLog_sound (w := (104489916001 / 395510083999)) (n := 12)
    (lo := (541215527 / 1000000000)) (hi := (67651941 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 145510083999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 145510083999) = 1/(145510083999 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15389 : Bounds (-67651941 / 125000000) (-541215527 / 1000000000) (Real.log (145510083999 / 250000000000)) := by
  have h := reflection_log_15389_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15390_neg : (4313119 / 8000000) ≤ -Real.log (145812426039 / 250000000000) ∧
    -Real.log (145812426039 / 250000000000) ≤ (134784969 / 250000000) := by
  have h := checkLog_sound (w := (104187573961 / 395812426039)) (n := 12)
    (lo := (4313119 / 8000000)) (hi := (134784969 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 145812426039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 145812426039) = 1/(145812426039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15390 : Bounds (-134784969 / 250000000) (-4313119 / 8000000) (Real.log (145812426039 / 250000000000)) := by
  have h := reflection_log_15390_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15391_neg : (11994561 / 7812500) ≤ -Real.log (250000000000 / 1160683956009) ∧
    -Real.log (250000000000 / 1160683956009) ≤ (1535303811 / 1000000000) := by
  have h := checkLog_sound (w := (160683956009 / 2160683956009)) (n := 12)
    (lo := (18626181 / 125000000)) (hi := (149009449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1160683956009 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1160683956009 / 1000000000000) = 1/(250000000000 / 1160683956009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15391 : Bounds (11994561 / 7812500) (1535303811 / 1000000000) (Real.log (1160683956009 / 250000000000)) := by
  have h := reflection_log_15391_neg
  have he : Real.log (1160683956009 / 250000000000) = -Real.log (250000000000 / 1160683956009) := by
    rw [show ((1160683956009 / 250000000000) : ℝ) = ((250000000000 / 1160683956009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15392_neg : (769258371 / 500000000) ≤ -Real.log (25000000000 / 116441915463) ∧
    -Real.log (25000000000 / 116441915463) ≤ (307703349 / 200000000) := by
  have h := checkLog_sound (w := (16441915463 / 216441915463)) (n := 12)
    (lo := (76111191 / 500000000)) (hi := (152222383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116441915463 / 100000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(116441915463 / 100000000000) = 1/(25000000000 / 116441915463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15392 : Bounds (769258371 / 500000000) (307703349 / 200000000) (Real.log (116441915463 / 25000000000)) := by
  have h := reflection_log_15392_neg
  have he : Real.log (116441915463 / 25000000000) = -Real.log (25000000000 / 116441915463) := by
    rw [show ((116441915463 / 25000000000) : ℝ) = ((25000000000 / 116441915463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15393_neg : (699464449 / 125000000) ≤ -Real.log (100000000000 / 26927027027027) ∧
    -Real.log (100000000000 / 26927027027027) ≤ (5595715601 / 1000000000) := by
  have h := checkLog_sound (w := (1327027027027 / 52527027027027)) (n := 12)
    (lo := (6317269 / 125000000)) (hi := (50538153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26927027027027 / 25600000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(26927027027027 / 25600000000000) = 1/(100000000000 / 26927027027027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15393 : Bounds (699464449 / 125000000) (5595715601 / 1000000000) (Real.log (26927027027027 / 100000000000)) := by
  have h := reflection_log_15393_neg
  have he : Real.log (26927027027027 / 100000000000) = -Real.log (100000000000 / 26927027027027) := by
    rw [show ((26927027027027 / 100000000000) : ℝ) = ((100000000000 / 26927027027027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15394_neg : (5623214933 / 1000000000) ≤ -Real.log (500000000000 / 138388888888889) ∧
    -Real.log (500000000000 / 138388888888889) ≤ (2811607471 / 500000000) := by
  have h := checkLog_sound (w := (10388888888889 / 266388888888889)) (n := 12)
    (lo := (78037493 / 1000000000)) (hi := (39018747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138388888888889 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(138388888888889 / 128000000000000) = 1/(500000000000 / 138388888888889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15394 : Bounds (5623214933 / 1000000000) (2811607471 / 500000000) (Real.log (138388888888889 / 500000000000)) := by
  have h := reflection_log_15394_neg
  have he : Real.log (138388888888889 / 500000000000) = -Real.log (500000000000 / 138388888888889) := by
    rw [show ((138388888888889 / 500000000000) : ℝ) = ((500000000000 / 138388888888889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15395_neg : (689641041 / 1000000000) ≤ -Real.log (1000 / 1993) ∧
    -Real.log (1000 / 1993) ≤ (344820521 / 500000000) := by
  have h := checkLog_sound (w := (993 / 2993)) (n := 12)
    (lo := (689641041 / 1000000000)) (hi := (344820521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1993 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1993 / 1000) = 1/(1000 / 1993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15395 : Bounds (689641041 / 1000000000) (344820521 / 500000000) (Real.log (1993 / 1000)) := by
  have h := reflection_log_15395_neg
  have he : Real.log (1993 / 1000) = -Real.log (1000 / 1993) := by
    rw [show ((1993 / 1000) : ℝ) = ((1000 / 1993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15396_neg : (2480922563 / 500000000) ≤ -Real.log (7 / 1000) ∧
    -Real.log (7 / 1000) ≤ (2480922567 / 500000000) := by
  have h := checkLog_sound (w := (13 / 237)) (n := 12)
    (lo := (54907433 / 500000000)) (hi := (109814867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 112) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(125 / 112) = 1/(7 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15396 : Bounds (-2480922567 / 500000000) (-2480922563 / 500000000) (Real.log (7 / 1000)) := by
  have h := reflection_log_15396_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15397_neg : (992507 / 1000000000) ≤ -Real.log (1000000 / 1000993) ∧
    -Real.log (1000000 / 1000993) ≤ (248127 / 250000000) := by
  have h := checkLog_sound (w := (993 / 2000993)) (n := 12)
    (lo := (992507 / 1000000000)) (hi := (248127 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000993 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000993 / 1000000) = 1/(1000000 / 1000993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15397 : Bounds (992507 / 1000000000) (248127 / 250000000) (Real.log (1000993 / 1000000)) := by
  have h := reflection_log_15397_neg
  have he : Real.log (1000993 / 1000000) = -Real.log (1000000 / 1000993) := by
    rw [show ((1000993 / 1000000) : ℝ) = ((1000000 / 1000993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15398_neg : (993493 / 1000000000) ≤ -Real.log (999007 / 1000000) ∧
    -Real.log (999007 / 1000000) ≤ (496747 / 500000000) := by
  have h := checkLog_sound (w := (993 / 1999007)) (n := 12)
    (lo := (993493 / 1000000000)) (hi := (496747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999007) = 1/(999007 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15398 : Bounds (-496747 / 500000000) (-993493 / 1000000000) (Real.log (999007 / 1000000)) := by
  have h := reflection_log_15398_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15399_neg : (498269119 / 1000000000) ≤ -Real.log (100000 / 164587) ∧
    -Real.log (100000 / 164587) ≤ (1557091 / 3125000) := by
  have h := checkLog_sound (w := (64587 / 264587)) (n := 12)
    (lo := (498269119 / 1000000000)) (hi := (1557091 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164587 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164587 / 100000) = 1/(100000 / 164587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15399 : Bounds (498269119 / 1000000000) (1557091 / 3125000) (Real.log (164587 / 100000)) := by
  have h := reflection_log_15399_neg
  have he : Real.log (164587 / 100000) = -Real.log (100000 / 164587) := by
    rw [show ((164587 / 100000) : ℝ) = ((100000 / 164587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15400_neg : (1038091201 / 1000000000) ≤ -Real.log (35413 / 100000) ∧
    -Real.log (35413 / 100000) ≤ (1038091203 / 1000000000) := by
  have h := checkLog_sound (w := (14587 / 85413)) (n := 12)
    (lo := (344944021 / 1000000000)) (hi := (172472011 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35413) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 35413) = 1/(35413 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15400 : Bounds (-1038091203 / 1000000000) (-1038091201 / 1000000000) (Real.log (35413 / 100000)) := by
  have h := reflection_log_15400_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15401_neg : (498838261 / 1000000000) ≤ -Real.log (1000000 / 1646807) ∧
    -Real.log (1000000 / 1646807) ≤ (249419131 / 500000000) := by
  have h := checkLog_sound (w := (646807 / 2646807)) (n := 12)
    (lo := (498838261 / 1000000000)) (hi := (249419131 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1646807 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1646807 / 1000000) = 1/(1000000 / 1646807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15401 : Bounds (498838261 / 1000000000) (249419131 / 500000000) (Real.log (1646807 / 1000000)) := by
  have h := reflection_log_15401_neg
  have he : Real.log (1646807 / 1000000) = -Real.log (1000000 / 1646807) := by
    rw [show ((1646807 / 1000000) : ℝ) = ((1000000 / 1646807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15402_neg : (260185157 / 250000000) ≤ -Real.log (353193 / 1000000) ∧
    -Real.log (353193 / 1000000) ≤ (104074063 / 100000000) := by
  have h := checkLog_sound (w := (146807 / 853193)) (n := 12)
    (lo := (43449181 / 125000000)) (hi := (347593449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 353193) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 353193) = 1/(353193 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15402 : Bounds (-104074063 / 100000000) (-260185157 / 250000000) (Real.log (353193 / 1000000)) := by
  have h := reflection_log_15402_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15403_neg : (541902367 / 1000000000) ≤ -Real.log (581640704751 / 1000000000000) ∧
    -Real.log (581640704751 / 1000000000000) ≤ (16934449 / 31250000) := by
  have h := checkLog_sound (w := (418359295249 / 1581640704751)) (n := 12)
    (lo := (541902367 / 1000000000)) (hi := (16934449 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 581640704751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 581640704751) = 1/(581640704751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15403 : Bounds (-16934449 / 31250000) (-541902367 / 1000000000) (Real.log (581640704751 / 1000000000000)) := by
  have h := reflection_log_15403_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15404_neg : (539822081 / 1000000000) ≤ -Real.log (5828519431 / 10000000000) ∧
    -Real.log (5828519431 / 10000000000) ≤ (269911041 / 500000000) := by
  have h := checkLog_sound (w := (4171480569 / 15828519431)) (n := 12)
    (lo := (539822081 / 1000000000)) (hi := (269911041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 5828519431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 5828519431) = 1/(5828519431 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15404 : Bounds (-269911041 / 500000000) (-539822081 / 1000000000) (Real.log (5828519431 / 10000000000)) := by
  have h := reflection_log_15404_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15405_neg : (2400563 / 1562500) ≤ -Real.log (50000000000 / 232382176037) ∧
    -Real.log (50000000000 / 232382176037) ≤ (1536360323 / 1000000000) := by
  have h := checkLog_sound (w := (32382176037 / 432382176037)) (n := 12)
    (lo := (3751649 / 25000000)) (hi := (150065961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((232382176037 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(232382176037 / 200000000000) = 1/(50000000000 / 232382176037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15405 : Bounds (2400563 / 1562500) (1536360323 / 1000000000) (Real.log (232382176037 / 50000000000)) := by
  have h := reflection_log_15405_neg
  have he : Real.log (232382176037 / 50000000000) = -Real.log (50000000000 / 232382176037) := by
    rw [show ((232382176037 / 50000000000) : ℝ) = ((50000000000 / 232382176037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15406_neg : (1539578889 / 1000000000) ≤ -Real.log (125000000000 / 582828297843) ∧
    -Real.log (125000000000 / 582828297843) ≤ (384894723 / 250000000) := by
  have h := checkLog_sound (w := (82828297843 / 1082828297843)) (n := 12)
    (lo := (153284529 / 1000000000)) (hi := (15328453 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((582828297843 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(582828297843 / 500000000000) = 1/(125000000000 / 582828297843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15406 : Bounds (1539578889 / 1000000000) (384894723 / 250000000) (Real.log (582828297843 / 125000000000)) := by
  have h := reflection_log_15406_neg
  have he : Real.log (582828297843 / 125000000000) = -Real.log (125000000000 / 582828297843) := by
    rw [show ((582828297843 / 125000000000) : ℝ) = ((125000000000 / 582828297843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15407_neg : (5623214933 / 1000000000) ≤ -Real.log (62500000000 / 17298611111111) ∧
    -Real.log (62500000000 / 17298611111111) ≤ (2811607471 / 500000000) := by
  have h := checkLog_sound (w := (1298611111111 / 33298611111111)) (n := 12)
    (lo := (78037493 / 1000000000)) (hi := (39018747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17298611111111 / 16000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(17298611111111 / 16000000000000) = 1/(62500000000 / 17298611111111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15407 : Bounds (5623214933 / 1000000000) (2811607471 / 500000000) (Real.log (17298611111111 / 62500000000)) := by
  have h := reflection_log_15407_neg
  have he : Real.log (17298611111111 / 62500000000) = -Real.log (62500000000 / 17298611111111) := by
    rw [show ((17298611111111 / 62500000000) : ℝ) = ((62500000000 / 17298611111111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15408_neg : (2825743083 / 500000000) ≤ -Real.log (500000000000 / 142357142857143) ∧
    -Real.log (500000000000 / 142357142857143) ≤ (226059447 / 40000000) := by
  have h := checkLog_sound (w := (14357142857143 / 270357142857143)) (n := 12)
    (lo := (53154363 / 500000000)) (hi := (106308727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142357142857143 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(142357142857143 / 128000000000000) = 1/(500000000000 / 142357142857143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15408 : Bounds (2825743083 / 500000000) (226059447 / 40000000) (Real.log (142357142857143 / 500000000000)) := by
  have h := reflection_log_15408_neg
  have he : Real.log (142357142857143 / 500000000000) = -Real.log (500000000000 / 142357142857143) := by
    rw [show ((142357142857143 / 500000000000) : ℝ) = ((500000000000 / 142357142857143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15409_neg : (689741387 / 1000000000) ≤ -Real.log (2500 / 4983) ∧
    -Real.log (2500 / 4983) ≤ (172435347 / 250000000) := by
  have h := checkLog_sound (w := (2483 / 7483)) (n := 12)
    (lo := (689741387 / 1000000000)) (hi := (172435347 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4983 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4983 / 2500) = 1/(2500 / 4983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15409 : Bounds (689741387 / 1000000000) (172435347 / 250000000) (Real.log (4983 / 2500)) := by
  have h := reflection_log_15409_neg
  have he : Real.log (4983 / 2500) = -Real.log (2500 / 4983) := by
    rw [show ((4983 / 2500) : ℝ) = ((2500 / 4983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15410_neg : (2495416331 / 500000000) ≤ -Real.log (17 / 2500) ∧
    -Real.log (17 / 2500) ≤ (499083267 / 100000000) := by
  have h := checkLog_sound (w := (81 / 1169)) (n := 12)
    (lo := (69401201 / 500000000)) (hi := (138802403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 544) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 544) = 1/(17 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15410 : Bounds (-499083267 / 100000000) (-2495416331 / 500000000) (Real.log (17 / 2500)) := by
  have h := reflection_log_15410_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15411_neg : (992707 / 1000000000) ≤ -Real.log (2500000 / 2502483) ∧
    -Real.log (2500000 / 2502483) ≤ (248177 / 250000000) := by
  have h := checkLog_sound (w := (2483 / 5002483)) (n := 12)
    (lo := (992707 / 1000000000)) (hi := (248177 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2502483 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2502483 / 2500000) = 1/(2500000 / 2502483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15411 : Bounds (992707 / 1000000000) (248177 / 250000000) (Real.log (2502483 / 2500000)) := by
  have h := reflection_log_15411_neg
  have he : Real.log (2502483 / 2500000) = -Real.log (2500000 / 2502483) := by
    rw [show ((2502483 / 2500000) : ℝ) = ((2500000 / 2502483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15412_neg : (993693 / 1000000000) ≤ -Real.log (2497517 / 2500000) ∧
    -Real.log (2497517 / 2500000) ≤ (496847 / 500000000) := by
  have h := checkLog_sound (w := (2483 / 4997517)) (n := 12)
    (lo := (993693 / 1000000000)) (hi := (496847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2497517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2497517) = 1/(2497517 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15412 : Bounds (-496847 / 500000000) (-993693 / 1000000000) (Real.log (2497517 / 2500000)) := by
  have h := reflection_log_15412_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15413_neg : (124614363 / 250000000) ≤ -Real.log (50000 / 82309) ∧
    -Real.log (50000 / 82309) ≤ (498457453 / 1000000000) := by
  have h := checkLog_sound (w := (32309 / 132309)) (n := 12)
    (lo := (124614363 / 250000000)) (hi := (498457453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82309 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82309 / 50000) = 1/(50000 / 82309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15413 : Bounds (124614363 / 250000000) (498457453 / 1000000000) (Real.log (82309 / 50000)) := by
  have h := reflection_log_15413_neg
  have he : Real.log (82309 / 50000) = -Real.log (50000 / 82309) := by
    rw [show ((82309 / 50000) : ℝ) = ((50000 / 82309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15414_neg : (1038966969 / 1000000000) ≤ -Real.log (17691 / 50000) ∧
    -Real.log (17691 / 50000) ≤ (1038966971 / 1000000000) := by
  have h := checkLog_sound (w := (7309 / 42691)) (n := 12)
    (lo := (345819789 / 1000000000)) (hi := (34581979 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 17691) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25000 / 17691) = 1/(17691 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15414 : Bounds (-1038966971 / 1000000000) (-1038966969 / 1000000000) (Real.log (17691 / 50000)) := by
  have h := reflection_log_15414_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15415_neg : (249513243 / 500000000) ≤ -Real.log (1000000 / 1647117) ∧
    -Real.log (1000000 / 1647117) ≤ (499026487 / 1000000000) := by
  have h := checkLog_sound (w := (647117 / 2647117)) (n := 12)
    (lo := (249513243 / 500000000)) (hi := (499026487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1647117 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1647117 / 1000000) = 1/(1000000 / 1647117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15415 : Bounds (249513243 / 500000000) (499026487 / 1000000000) (Real.log (1647117 / 1000000)) := by
  have h := reflection_log_15415_neg
  have he : Real.log (1647117 / 1000000) = -Real.log (1000000 / 1647117) := by
    rw [show ((1647117 / 1000000) : ℝ) = ((1000000 / 1647117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15416_neg : (1041618721 / 1000000000) ≤ -Real.log (352883 / 1000000) ∧
    -Real.log (352883 / 1000000) ≤ (1041618723 / 1000000000) := by
  have h := checkLog_sound (w := (147117 / 852883)) (n := 12)
    (lo := (348471541 / 1000000000)) (hi := (174235771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 352883) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 352883) = 1/(352883 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15416 : Bounds (-1041618723 / 1000000000) (-1041618721 / 1000000000) (Real.log (352883 / 1000000)) := by
  have h := reflection_log_15416_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15417_neg : (271296117 / 500000000) ≤ -Real.log (581239588311 / 1000000000000) ∧
    -Real.log (581239588311 / 1000000000000) ≤ (108518447 / 200000000) := by
  have h := checkLog_sound (w := (418760411689 / 1581239588311)) (n := 12)
    (lo := (271296117 / 500000000)) (hi := (108518447 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 581239588311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 581239588311) = 1/(581239588311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15417 : Bounds (-108518447 / 200000000) (-271296117 / 500000000) (Real.log (581239588311 / 1000000000000)) := by
  have h := reflection_log_15417_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15418_neg : (540509517 / 1000000000) ≤ -Real.log (1456128519 / 2500000000) ∧
    -Real.log (1456128519 / 2500000000) ≤ (270254759 / 500000000) := by
  have h := checkLog_sound (w := (1043871481 / 3956128519)) (n := 12)
    (lo := (540509517 / 1000000000)) (hi := (270254759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 1456128519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 1456128519) = 1/(1456128519 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15418 : Bounds (-270254759 / 500000000) (-540509517 / 1000000000) (Real.log (1456128519 / 2500000000)) := by
  have h := reflection_log_15418_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15419_neg : (76871221 / 50000000) ≤ -Real.log (10000000000 / 46525917133) ∧
    -Real.log (10000000000 / 46525917133) ≤ (1537424423 / 1000000000) := by
  have h := checkLog_sound (w := (6525917133 / 86525917133)) (n := 12)
    (lo := (7556503 / 50000000)) (hi := (151130061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46525917133 / 40000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(46525917133 / 40000000000) = 1/(10000000000 / 46525917133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15419 : Bounds (76871221 / 50000000) (1537424423 / 1000000000) (Real.log (46525917133 / 10000000000)) := by
  have h := reflection_log_15419_neg
  have he : Real.log (46525917133 / 10000000000) = -Real.log (10000000000 / 46525917133) := by
    rw [show ((46525917133 / 10000000000) : ℝ) = ((10000000000 / 46525917133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15420_neg : (1540645207 / 1000000000) ≤ -Real.log (250000000000 / 1166900219053) ∧
    -Real.log (250000000000 / 1166900219053) ≤ (154064521 / 100000000) := by
  have h := checkLog_sound (w := (166900219053 / 2166900219053)) (n := 12)
    (lo := (154350847 / 1000000000)) (hi := (602933 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1166900219053 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1166900219053 / 1000000000000) = 1/(250000000000 / 1166900219053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15420 : Bounds (1540645207 / 1000000000) (154064521 / 100000000) (Real.log (1166900219053 / 250000000000)) := by
  have h := reflection_log_15420_neg
  have he : Real.log (1166900219053 / 250000000000) = -Real.log (250000000000 / 1166900219053) := by
    rw [show ((1166900219053 / 250000000000) : ℝ) = ((250000000000 / 1166900219053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15421_neg : (2825743083 / 500000000) ≤ -Real.log (250000000000 / 71178571428571) ∧
    -Real.log (250000000000 / 71178571428571) ≤ (226059447 / 40000000) := by
  have h := checkLog_sound (w := (7178571428571 / 135178571428571)) (n := 12)
    (lo := (53154363 / 500000000)) (hi := (106308727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71178571428571 / 64000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(71178571428571 / 64000000000000) = 1/(250000000000 / 71178571428571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15421 : Bounds (2825743083 / 500000000) (226059447 / 40000000) (Real.log (71178571428571 / 250000000000)) := by
  have h := reflection_log_15421_neg
  have he : Real.log (71178571428571 / 250000000000) = -Real.log (250000000000 / 71178571428571) := by
    rw [show ((71178571428571 / 250000000000) : ℝ) = ((250000000000 / 71178571428571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15422_neg : (5680574049 / 1000000000) ≤ -Real.log (125000000000 / 36639705882353) ∧
    -Real.log (125000000000 / 36639705882353) ≤ (2840287029 / 500000000) := by
  have h := checkLog_sound (w := (4639705882353 / 68639705882353)) (n := 12)
    (lo := (135396609 / 1000000000)) (hi := (13539661 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36639705882353 / 32000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(36639705882353 / 32000000000000) = 1/(125000000000 / 36639705882353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15422 : Bounds (5680574049 / 1000000000) (2840287029 / 500000000) (Real.log (36639705882353 / 125000000000)) := by
  have h := reflection_log_15422_neg
  have he : Real.log (36639705882353 / 125000000000) = -Real.log (125000000000 / 36639705882353) := by
    rw [show ((36639705882353 / 125000000000) : ℝ) = ((125000000000 / 36639705882353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15423_neg : (689841723 / 1000000000) ≤ -Real.log (5000 / 9967) ∧
    -Real.log (5000 / 9967) ≤ (172460431 / 250000000) := by
  have h := checkLog_sound (w := (4967 / 14967)) (n := 12)
    (lo := (689841723 / 1000000000)) (hi := (172460431 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9967 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9967 / 5000) = 1/(5000 / 9967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15423 : Bounds (689841723 / 1000000000) (172460431 / 250000000) (Real.log (9967 / 5000)) := by
  have h := reflection_log_15423_neg
  have he : Real.log (9967 / 5000) = -Real.log (5000 / 9967) := by
    rw [show ((9967 / 5000) : ℝ) = ((5000 / 9967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
