import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2048_neg : (8634687 / 100000000) ≤ -Real.log (229319 / 250000) ∧
    -Real.log (229319 / 250000) ≤ (86346871 / 1000000000) := by
  have h := checkLog_sound (w := (20681 / 479319)) (n := 12)
    (lo := (8634687 / 100000000)) (hi := (86346871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229319) = 1/(229319 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2048 : Bounds (-86346871 / 1000000000) (-8634687 / 100000000) (Real.log (229319 / 250000)) := by
  have h := reflection_log_2048_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2049_neg : (19919891 / 250000000) ≤ -Real.log (50000 / 54147) ∧
    -Real.log (50000 / 54147) ≤ (15935913 / 200000000) := by
  have h := checkLog_sound (w := (4147 / 104147)) (n := 12)
    (lo := (19919891 / 250000000)) (hi := (15935913 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54147 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54147 / 50000) = 1/(50000 / 54147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2049 : Bounds (19919891 / 250000000) (15935913 / 200000000) (Real.log (54147 / 50000)) := by
  have h := reflection_log_2049_neg
  have he : Real.log (54147 / 50000) = -Real.log (50000 / 54147) := by
    rw [show ((54147 / 50000) : ℝ) = ((50000 / 54147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2050_neg : (43291189 / 500000000) ≤ -Real.log (45853 / 50000) ∧
    -Real.log (45853 / 50000) ≤ (86582379 / 1000000000) := by
  have h := checkLog_sound (w := (4147 / 95853)) (n := 12)
    (lo := (43291189 / 500000000)) (hi := (86582379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45853) = 1/(45853 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2050 : Bounds (-86582379 / 1000000000) (-43291189 / 500000000) (Real.log (45853 / 50000)) := by
  have h := reflection_log_2050_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2051_neg : (6902813 / 1000000000) ≤ -Real.log (2482802391 / 2500000000) ∧
    -Real.log (2482802391 / 2500000000) ≤ (3451407 / 500000000) := by
  have h := checkLog_sound (w := (17197609 / 4982802391)) (n := 12)
    (lo := (6902813 / 1000000000)) (hi := (3451407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2482802391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2482802391) = 1/(2482802391 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2051 : Bounds (-3451407 / 500000000) (-6902813 / 1000000000) (Real.log (2482802391 / 2500000000)) := by
  have h := reflection_log_2051_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2052_neg : (3433391 / 500000000) ≤ -Real.log (62072296239 / 62500000000) ∧
    -Real.log (62072296239 / 62500000000) ≤ (6866783 / 1000000000) := by
  have h := checkLog_sound (w := (427703761 / 124572296239)) (n := 12)
    (lo := (3433391 / 500000000)) (hi := (6866783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62072296239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62072296239) = 1/(62072296239 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2052 : Bounds (-6866783 / 1000000000) (-3433391 / 500000000) (Real.log (62072296239 / 62500000000)) := by
  have h := reflection_log_2052_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2053_neg : (82913479 / 500000000) ≤ -Real.log (100000000000 / 118036883119) ∧
    -Real.log (100000000000 / 118036883119) ≤ (165826959 / 1000000000) := by
  have h := checkLog_sound (w := (18036883119 / 218036883119)) (n := 12)
    (lo := (82913479 / 500000000)) (hi := (165826959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118036883119 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118036883119 / 100000000000) = 1/(100000000000 / 118036883119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2053 : Bounds (82913479 / 500000000) (165826959 / 1000000000) (Real.log (118036883119 / 100000000000)) := by
  have h := reflection_log_2053_neg
  have he : Real.log (118036883119 / 100000000000) = -Real.log (100000000000 / 118036883119) := by
    rw [show ((118036883119 / 100000000000) : ℝ) = ((100000000000 / 118036883119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2054_neg : (83130971 / 500000000) ≤ -Real.log (500000000000 / 590441192507) ∧
    -Real.log (500000000000 / 590441192507) ≤ (166261943 / 1000000000) := by
  have h := checkLog_sound (w := (90441192507 / 1090441192507)) (n := 12)
    (lo := (83130971 / 500000000)) (hi := (166261943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590441192507 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590441192507 / 500000000000) = 1/(500000000000 / 590441192507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2054 : Bounds (83130971 / 500000000) (166261943 / 1000000000) (Real.log (590441192507 / 500000000000)) := by
  have h := reflection_log_2054_neg
  have he : Real.log (590441192507 / 500000000000) = -Real.log (500000000000 / 590441192507) := by
    rw [show ((590441192507 / 500000000000) : ℝ) = ((500000000000 / 590441192507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2055_neg : (16631673 / 50000000) ≤ -Real.log (250000000000 / 348659003831) ∧
    -Real.log (250000000000 / 348659003831) ≤ (332633461 / 1000000000) := by
  have h := checkLog_sound (w := (98659003831 / 598659003831)) (n := 12)
    (lo := (16631673 / 50000000)) (hi := (332633461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((348659003831 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(348659003831 / 250000000000) = 1/(250000000000 / 348659003831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2055 : Bounds (16631673 / 50000000) (332633461 / 1000000000) (Real.log (348659003831 / 250000000000)) := by
  have h := reflection_log_2055_neg
  have he : Real.log (348659003831 / 250000000000) = -Real.log (250000000000 / 348659003831) := by
    rw [show ((348659003831 / 250000000000) : ℝ) = ((250000000000 / 348659003831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2056_neg : (332839047 / 1000000000) ≤ -Real.log (500000000000 / 697461381871) ∧
    -Real.log (500000000000 / 697461381871) ≤ (41604881 / 125000000) := by
  have h := checkLog_sound (w := (197461381871 / 1197461381871)) (n := 12)
    (lo := (332839047 / 1000000000)) (hi := (41604881 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697461381871 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697461381871 / 500000000000) = 1/(500000000000 / 697461381871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2056 : Bounds (332839047 / 1000000000) (41604881 / 125000000) (Real.log (697461381871 / 500000000000)) := by
  have h := reflection_log_2056_neg
  have he : Real.log (697461381871 / 500000000000) = -Real.log (500000000000 / 697461381871) := by
    rw [show ((697461381871 / 500000000000) : ℝ) = ((500000000000 / 697461381871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2057_neg : (152721087 / 1000000000) ≤ -Real.log (200 / 233) ∧
    -Real.log (200 / 233) ≤ (2386267 / 15625000) := by
  have h := checkLog_sound (w := (33 / 433)) (n := 12)
    (lo := (152721087 / 1000000000)) (hi := (2386267 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233 / 200) = 1/(200 / 233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2057 : Bounds (152721087 / 1000000000) (2386267 / 15625000) (Real.log (233 / 200)) := by
  have h := reflection_log_2057_neg
  have he : Real.log (233 / 200) = -Real.log (200 / 233) := by
    rw [show ((233 / 200) : ℝ) = ((200 / 233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2058_neg : (90161777 / 500000000) ≤ -Real.log (167 / 200) ∧
    -Real.log (167 / 200) ≤ (36064711 / 200000000) := by
  have h := checkLog_sound (w := (33 / 367)) (n := 12)
    (lo := (90161777 / 500000000)) (hi := (36064711 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 167) = 1/(167 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2058 : Bounds (-36064711 / 200000000) (-90161777 / 500000000) (Real.log (167 / 200)) := by
  have h := reflection_log_2058_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2059_neg : (82493 / 500000000) ≤ -Real.log (200000 / 200033) ∧
    -Real.log (200000 / 200033) ≤ (164987 / 1000000000) := by
  have h := checkLog_sound (w := (33 / 400033)) (n := 12)
    (lo := (82493 / 500000000)) (hi := (164987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200033 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200033 / 200000) = 1/(200000 / 200033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2059 : Bounds (82493 / 500000000) (164987 / 1000000000) (Real.log (200033 / 200000)) := by
  have h := reflection_log_2059_neg
  have he : Real.log (200033 / 200000) = -Real.log (200000 / 200033) := by
    rw [show ((200033 / 200000) : ℝ) = ((200000 / 200033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2060_neg : (165013 / 1000000000) ≤ -Real.log (199967 / 200000) ∧
    -Real.log (199967 / 200000) ≤ (82507 / 500000000) := by
  have h := checkLog_sound (w := (33 / 399967)) (n := 12)
    (lo := (165013 / 1000000000)) (hi := (82507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199967) = 1/(199967 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2060 : Bounds (-82507 / 500000000) (-165013 / 1000000000) (Real.log (199967 / 200000)) := by
  have h := reflection_log_2060_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2061_neg : (7952719 / 100000000) ≤ -Real.log (40000 / 43311) ∧
    -Real.log (40000 / 43311) ≤ (79527191 / 1000000000) := by
  have h := checkLog_sound (w := (3311 / 83311)) (n := 12)
    (lo := (7952719 / 100000000)) (hi := (79527191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43311 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43311 / 40000) = 1/(40000 / 43311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2061 : Bounds (7952719 / 100000000) (79527191 / 1000000000) (Real.log (43311 / 40000)) := by
  have h := reflection_log_2061_neg
  have he : Real.log (43311 / 40000) = -Real.log (40000 / 43311) := by
    rw [show ((43311 / 40000) : ℝ) = ((40000 / 43311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2062_neg : (86402471 / 1000000000) ≤ -Real.log (36689 / 40000) ∧
    -Real.log (36689 / 40000) ≤ (10800309 / 125000000) := by
  have h := checkLog_sound (w := (3311 / 76689)) (n := 12)
    (lo := (86402471 / 1000000000)) (hi := (10800309 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 36689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 36689) = 1/(36689 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2062 : Bounds (-10800309 / 125000000) (-86402471 / 1000000000) (Real.log (36689 / 40000)) := by
  have h := reflection_log_2062_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2063_neg : (79726657 / 1000000000) ≤ -Real.log (1000000 / 1082991) ∧
    -Real.log (1000000 / 1082991) ≤ (39863329 / 500000000) := by
  have h := checkLog_sound (w := (82991 / 2082991)) (n := 12)
    (lo := (79726657 / 1000000000)) (hi := (39863329 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082991 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082991 / 1000000) = 1/(1000000 / 1082991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2063 : Bounds (79726657 / 1000000000) (39863329 / 500000000) (Real.log (1082991 / 1000000)) := by
  have h := reflection_log_2063_neg
  have he : Real.log (1082991 / 1000000) = -Real.log (1000000 / 1082991) := by
    rw [show ((1082991 / 1000000) : ℝ) = ((1000000 / 1082991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2064_neg : (10829749 / 125000000) ≤ -Real.log (917009 / 1000000) ∧
    -Real.log (917009 / 1000000) ≤ (86637993 / 1000000000) := by
  have h := checkLog_sound (w := (82991 / 1917009)) (n := 12)
    (lo := (10829749 / 125000000)) (hi := (86637993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917009) = 1/(917009 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2064 : Bounds (-86637993 / 1000000000) (-10829749 / 125000000) (Real.log (917009 / 1000000)) := by
  have h := reflection_log_2064_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2065_neg : (3455667 / 500000000) ≤ -Real.log (993112493919 / 1000000000000) ∧
    -Real.log (993112493919 / 1000000000000) ≤ (1382267 / 200000000) := by
  have h := checkLog_sound (w := (6887506081 / 1993112493919)) (n := 12)
    (lo := (3455667 / 500000000)) (hi := (1382267 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993112493919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993112493919) = 1/(993112493919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2065 : Bounds (-1382267 / 200000000) (-3455667 / 500000000) (Real.log (993112493919 / 1000000000000)) := by
  have h := reflection_log_2065_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2066_neg : (6875281 / 1000000000) ≤ -Real.log (1589037279 / 1600000000) ∧
    -Real.log (1589037279 / 1600000000) ≤ (3437641 / 500000000) := by
  have h := checkLog_sound (w := (10962721 / 3189037279)) (n := 12)
    (lo := (6875281 / 1000000000)) (hi := (3437641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1589037279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1589037279) = 1/(1589037279 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2066 : Bounds (-3437641 / 500000000) (-6875281 / 1000000000) (Real.log (1589037279 / 1600000000)) := by
  have h := reflection_log_2066_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2067_neg : (165929661 / 1000000000) ≤ -Real.log (500000000000 / 590245032571) ∧
    -Real.log (500000000000 / 590245032571) ≤ (82964831 / 500000000) := by
  have h := checkLog_sound (w := (90245032571 / 1090245032571)) (n := 12)
    (lo := (165929661 / 1000000000)) (hi := (82964831 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590245032571 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590245032571 / 500000000000) = 1/(500000000000 / 590245032571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2067 : Bounds (165929661 / 1000000000) (82964831 / 500000000) (Real.log (590245032571 / 500000000000)) := by
  have h := reflection_log_2067_neg
  have he : Real.log (590245032571 / 500000000000) = -Real.log (500000000000 / 590245032571) := by
    rw [show ((590245032571 / 500000000000) : ℝ) = ((500000000000 / 590245032571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2068_neg : (166364649 / 1000000000) ≤ -Real.log (500000000000 / 590501838041) ∧
    -Real.log (500000000000 / 590501838041) ≤ (3327293 / 20000000) := by
  have h := checkLog_sound (w := (90501838041 / 1090501838041)) (n := 12)
    (lo := (166364649 / 1000000000)) (hi := (3327293 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590501838041 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590501838041 / 500000000000) = 1/(500000000000 / 590501838041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2068 : Bounds (166364649 / 1000000000) (3327293 / 20000000) (Real.log (590501838041 / 500000000000)) := by
  have h := reflection_log_2068_neg
  have he : Real.log (590501838041 / 500000000000) = -Real.log (500000000000 / 590501838041) := by
    rw [show ((590501838041 / 500000000000) : ℝ) = ((500000000000 / 590501838041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2069_neg : (332839047 / 1000000000) ≤ -Real.log (50000000000 / 69746138187) ∧
    -Real.log (50000000000 / 69746138187) ≤ (41604881 / 125000000) := by
  have h := checkLog_sound (w := (19746138187 / 119746138187)) (n := 12)
    (lo := (332839047 / 1000000000)) (hi := (41604881 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69746138187 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69746138187 / 50000000000) = 1/(50000000000 / 69746138187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2069 : Bounds (332839047 / 1000000000) (41604881 / 125000000) (Real.log (69746138187 / 50000000000)) := by
  have h := reflection_log_2069_neg
  have he : Real.log (69746138187 / 50000000000) = -Real.log (50000000000 / 69746138187) := by
    rw [show ((69746138187 / 50000000000) : ℝ) = ((50000000000 / 69746138187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2070_neg : (333044641 / 1000000000) ≤ -Real.log (25000000000 / 34880239521) ∧
    -Real.log (25000000000 / 34880239521) ≤ (166522321 / 500000000) := by
  have h := checkLog_sound (w := (9880239521 / 59880239521)) (n := 12)
    (lo := (333044641 / 1000000000)) (hi := (166522321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34880239521 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34880239521 / 25000000000) = 1/(25000000000 / 34880239521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2070 : Bounds (333044641 / 1000000000) (166522321 / 500000000) (Real.log (34880239521 / 25000000000)) := by
  have h := reflection_log_2070_neg
  have he : Real.log (34880239521 / 25000000000) = -Real.log (25000000000 / 34880239521) := by
    rw [show ((34880239521 / 25000000000) : ℝ) = ((25000000000 / 34880239521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2071_neg : (3820173 / 25000000) ≤ -Real.log (10000 / 11651) ∧
    -Real.log (10000 / 11651) ≤ (152806921 / 1000000000) := by
  have h := checkLog_sound (w := (1651 / 21651)) (n := 12)
    (lo := (3820173 / 25000000)) (hi := (152806921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11651 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11651 / 10000) = 1/(10000 / 11651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2071 : Bounds (3820173 / 25000000) (152806921 / 1000000000) (Real.log (11651 / 10000)) := by
  have h := reflection_log_2071_neg
  have he : Real.log (11651 / 10000) = -Real.log (10000 / 11651) := by
    rw [show ((11651 / 10000) : ℝ) = ((10000 / 11651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2072_neg : (180443321 / 1000000000) ≤ -Real.log (8349 / 10000) ∧
    -Real.log (8349 / 10000) ≤ (90221661 / 500000000) := by
  have h := checkLog_sound (w := (1651 / 18349)) (n := 12)
    (lo := (180443321 / 1000000000)) (hi := (90221661 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8349) = 1/(8349 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2072 : Bounds (-90221661 / 500000000) (-180443321 / 1000000000) (Real.log (8349 / 10000)) := by
  have h := reflection_log_2072_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2073_neg : (82543 / 500000000) ≤ -Real.log (10000000 / 10001651) ∧
    -Real.log (10000000 / 10001651) ≤ (165087 / 1000000000) := by
  have h := checkLog_sound (w := (1651 / 20001651)) (n := 12)
    (lo := (82543 / 500000000)) (hi := (165087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001651 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001651 / 10000000) = 1/(10000000 / 10001651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2073 : Bounds (82543 / 500000000) (165087 / 1000000000) (Real.log (10001651 / 10000000)) := by
  have h := reflection_log_2073_neg
  have he : Real.log (10001651 / 10000000) = -Real.log (10000000 / 10001651) := by
    rw [show ((10001651 / 10000000) : ℝ) = ((10000000 / 10001651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2074_neg : (165113 / 1000000000) ≤ -Real.log (9998349 / 10000000) ∧
    -Real.log (9998349 / 10000000) ≤ (82557 / 500000000) := by
  have h := checkLog_sound (w := (1651 / 19998349)) (n := 12)
    (lo := (165113 / 1000000000)) (hi := (82557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998349) = 1/(9998349 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2074 : Bounds (-82557 / 500000000) (-165113 / 1000000000) (Real.log (9998349 / 10000000)) := by
  have h := reflection_log_2074_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2075_neg : (7957429 / 100000000) ≤ -Real.log (500000 / 541413) ∧
    -Real.log (500000 / 541413) ≤ (79574291 / 1000000000) := by
  have h := checkLog_sound (w := (41413 / 1041413)) (n := 12)
    (lo := (7957429 / 100000000)) (hi := (79574291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541413 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541413 / 500000) = 1/(500000 / 541413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2075 : Bounds (7957429 / 100000000) (79574291 / 1000000000) (Real.log (541413 / 500000)) := by
  have h := reflection_log_2075_neg
  have he : Real.log (541413 / 500000) = -Real.log (500000 / 541413) := by
    rw [show ((541413 / 500000) : ℝ) = ((500000 / 541413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2076_neg : (3458323 / 40000000) ≤ -Real.log (458587 / 500000) ∧
    -Real.log (458587 / 500000) ≤ (21614519 / 250000000) := by
  have h := checkLog_sound (w := (41413 / 958587)) (n := 12)
    (lo := (3458323 / 40000000)) (hi := (21614519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458587) = 1/(458587 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2076 : Bounds (-21614519 / 250000000) (-3458323 / 40000000) (Real.log (458587 / 500000)) := by
  have h := reflection_log_2076_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2077_neg : (19943437 / 250000000) ≤ -Real.log (500000 / 541521) ∧
    -Real.log (500000 / 541521) ≤ (79773749 / 1000000000) := by
  have h := checkLog_sound (w := (41521 / 1041521)) (n := 12)
    (lo := (19943437 / 250000000)) (hi := (79773749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541521 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541521 / 500000) = 1/(500000 / 541521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2077 : Bounds (19943437 / 250000000) (79773749 / 1000000000) (Real.log (541521 / 500000)) := by
  have h := reflection_log_2077_neg
  have he : Real.log (541521 / 500000) = -Real.log (500000 / 541521) := by
    rw [show ((541521 / 500000) : ℝ) = ((500000 / 541521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2078_neg : (86693609 / 1000000000) ≤ -Real.log (458479 / 500000) ∧
    -Real.log (458479 / 500000) ≤ (8669361 / 100000000) := by
  have h := checkLog_sound (w := (41521 / 958479)) (n := 12)
    (lo := (86693609 / 1000000000)) (hi := (8669361 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458479) = 1/(458479 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2078 : Bounds (-8669361 / 100000000) (-86693609 / 1000000000) (Real.log (458479 / 500000)) := by
  have h := reflection_log_2078_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2079_neg : (345993 / 50000000) ≤ -Real.log (248276006559 / 250000000000) ∧
    -Real.log (248276006559 / 250000000000) ≤ (6919861 / 1000000000) := by
  have h := checkLog_sound (w := (1723993441 / 498276006559)) (n := 12)
    (lo := (345993 / 50000000)) (hi := (6919861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248276006559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248276006559) = 1/(248276006559 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2079 : Bounds (-6919861 / 1000000000) (-345993 / 50000000) (Real.log (248276006559 / 250000000000)) := by
  have h := reflection_log_2079_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2080_neg : (1376757 / 200000000) ≤ -Real.log (248284963431 / 250000000000) ∧
    -Real.log (248284963431 / 250000000000) ≤ (3441893 / 500000000) := by
  have h := checkLog_sound (w := (1715036569 / 498284963431)) (n := 12)
    (lo := (1376757 / 200000000)) (hi := (3441893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248284963431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248284963431) = 1/(248284963431 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2080 : Bounds (-3441893 / 500000000) (-1376757 / 200000000) (Real.log (248284963431 / 250000000000)) := by
  have h := reflection_log_2080_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2081_neg : (33206473 / 200000000) ≤ -Real.log (500000000000 / 590305656287) ∧
    -Real.log (500000000000 / 590305656287) ≤ (83016183 / 500000000) := by
  have h := checkLog_sound (w := (90305656287 / 1090305656287)) (n := 12)
    (lo := (33206473 / 200000000)) (hi := (83016183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590305656287 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590305656287 / 500000000000) = 1/(500000000000 / 590305656287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2081 : Bounds (33206473 / 200000000) (83016183 / 500000000) (Real.log (590305656287 / 500000000000)) := by
  have h := reflection_log_2081_neg
  have he : Real.log (590305656287 / 500000000000) = -Real.log (500000000000 / 590305656287) := by
    rw [show ((590305656287 / 500000000000) : ℝ) = ((500000000000 / 590305656287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2082_neg : (166467357 / 1000000000) ≤ -Real.log (250000000000 / 295281245161) ∧
    -Real.log (250000000000 / 295281245161) ≤ (83233679 / 500000000) := by
  have h := checkLog_sound (w := (45281245161 / 545281245161)) (n := 12)
    (lo := (166467357 / 1000000000)) (hi := (83233679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295281245161 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295281245161 / 250000000000) = 1/(250000000000 / 295281245161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2082 : Bounds (166467357 / 1000000000) (83233679 / 500000000) (Real.log (295281245161 / 250000000000)) := by
  have h := reflection_log_2082_neg
  have he : Real.log (295281245161 / 250000000000) = -Real.log (250000000000 / 295281245161) := by
    rw [show ((295281245161 / 250000000000) : ℝ) = ((250000000000 / 295281245161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2083_neg : (333044641 / 1000000000) ≤ -Real.log (500000000000 / 697604790419) ∧
    -Real.log (500000000000 / 697604790419) ≤ (166522321 / 500000000) := by
  have h := checkLog_sound (w := (197604790419 / 1197604790419)) (n := 12)
    (lo := (333044641 / 1000000000)) (hi := (166522321 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697604790419 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697604790419 / 500000000000) = 1/(500000000000 / 697604790419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2083 : Bounds (333044641 / 1000000000) (166522321 / 500000000) (Real.log (697604790419 / 500000000000)) := by
  have h := reflection_log_2083_neg
  have he : Real.log (697604790419 / 500000000000) = -Real.log (500000000000 / 697604790419) := by
    rw [show ((697604790419 / 500000000000) : ℝ) = ((500000000000 / 697604790419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2084_neg : (166625121 / 500000000) ≤ -Real.log (250000000000 / 348874116661) ∧
    -Real.log (250000000000 / 348874116661) ≤ (333250243 / 1000000000) := by
  have h := checkLog_sound (w := (98874116661 / 598874116661)) (n := 12)
    (lo := (166625121 / 500000000)) (hi := (333250243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((348874116661 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(348874116661 / 250000000000) = 1/(250000000000 / 348874116661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2084 : Bounds (166625121 / 500000000) (333250243 / 1000000000) (Real.log (348874116661 / 250000000000)) := by
  have h := reflection_log_2084_neg
  have he : Real.log (348874116661 / 250000000000) = -Real.log (250000000000 / 348874116661) := by
    rw [show ((348874116661 / 250000000000) : ℝ) = ((250000000000 / 348874116661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2085_neg : (76446373 / 500000000) ≤ -Real.log (2500 / 2913) ∧
    -Real.log (2500 / 2913) ≤ (152892747 / 1000000000) := by
  have h := checkLog_sound (w := (413 / 5413)) (n := 12)
    (lo := (76446373 / 500000000)) (hi := (152892747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2913 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2913 / 2500) = 1/(2500 / 2913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2085 : Bounds (76446373 / 500000000) (152892747 / 1000000000) (Real.log (2913 / 2500)) := by
  have h := reflection_log_2085_neg
  have he : Real.log (2913 / 2500) = -Real.log (2500 / 2913) := by
    rw [show ((2913 / 2500) : ℝ) = ((2500 / 2913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2086_neg : (180563103 / 1000000000) ≤ -Real.log (2087 / 2500) ∧
    -Real.log (2087 / 2500) ≤ (5642597 / 31250000) := by
  have h := checkLog_sound (w := (413 / 4587)) (n := 12)
    (lo := (180563103 / 1000000000)) (hi := (5642597 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2087) = 1/(2087 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2086 : Bounds (-5642597 / 31250000) (-180563103 / 1000000000) (Real.log (2087 / 2500)) := by
  have h := reflection_log_2086_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2087_neg : (82593 / 500000000) ≤ -Real.log (2500000 / 2500413) ∧
    -Real.log (2500000 / 2500413) ≤ (165187 / 1000000000) := by
  have h := checkLog_sound (w := (413 / 5000413)) (n := 12)
    (lo := (82593 / 500000000)) (hi := (165187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500413 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500413 / 2500000) = 1/(2500000 / 2500413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2087 : Bounds (82593 / 500000000) (165187 / 1000000000) (Real.log (2500413 / 2500000)) := by
  have h := reflection_log_2087_neg
  have he : Real.log (2500413 / 2500000) = -Real.log (2500000 / 2500413) := by
    rw [show ((2500413 / 2500000) : ℝ) = ((2500000 / 2500413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2088_neg : (165213 / 1000000000) ≤ -Real.log (2499587 / 2500000) ∧
    -Real.log (2499587 / 2500000) ≤ (82607 / 500000000) := by
  have h := checkLog_sound (w := (413 / 4999587)) (n := 12)
    (lo := (165213 / 1000000000)) (hi := (82607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499587) = 1/(2499587 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2088 : Bounds (-82607 / 500000000) (-165213 / 1000000000) (Real.log (2499587 / 2500000)) := by
  have h := reflection_log_2088_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2089_neg : (4976279 / 62500000) ≤ -Real.log (250000 / 270719) ∧
    -Real.log (250000 / 270719) ≤ (15924093 / 200000000) := by
  have h := checkLog_sound (w := (20719 / 520719)) (n := 12)
    (lo := (4976279 / 62500000)) (hi := (15924093 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270719 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270719 / 250000) = 1/(250000 / 270719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2089 : Bounds (4976279 / 62500000) (15924093 / 200000000) (Real.log (270719 / 250000)) := by
  have h := reflection_log_2089_neg
  have he : Real.log (270719 / 250000) = -Real.log (250000 / 270719) := by
    rw [show ((270719 / 250000) : ℝ) = ((250000 / 270719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2090_neg : (5407037 / 62500000) ≤ -Real.log (229281 / 250000) ∧
    -Real.log (229281 / 250000) ≤ (86512593 / 1000000000) := by
  have h := checkLog_sound (w := (20719 / 479281)) (n := 12)
    (lo := (5407037 / 62500000)) (hi := (86512593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229281) = 1/(229281 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2090 : Bounds (-86512593 / 1000000000) (-5407037 / 62500000) (Real.log (229281 / 250000)) := by
  have h := reflection_log_2090_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2091_neg : (79819913 / 1000000000) ≤ -Real.log (250000 / 270773) ∧
    -Real.log (250000 / 270773) ≤ (39909957 / 500000000) := by
  have h := checkLog_sound (w := (20773 / 520773)) (n := 12)
    (lo := (79819913 / 1000000000)) (hi := (39909957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270773 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270773 / 250000) = 1/(250000 / 270773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2091 : Bounds (79819913 / 1000000000) (39909957 / 500000000) (Real.log (270773 / 250000)) := by
  have h := reflection_log_2091_neg
  have he : Real.log (270773 / 250000) = -Real.log (250000 / 270773) := by
    rw [show ((270773 / 250000) : ℝ) = ((250000 / 270773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2092_neg : (43374069 / 500000000) ≤ -Real.log (229227 / 250000) ∧
    -Real.log (229227 / 250000) ≤ (86748139 / 1000000000) := by
  have h := checkLog_sound (w := (20773 / 479227)) (n := 12)
    (lo := (43374069 / 500000000)) (hi := (86748139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229227) = 1/(229227 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2092 : Bounds (-86748139 / 1000000000) (-43374069 / 500000000) (Real.log (229227 / 250000)) := by
  have h := reflection_log_2092_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2093_neg : (277129 / 40000000) ≤ -Real.log (62068482471 / 62500000000) ∧
    -Real.log (62068482471 / 62500000000) ≤ (3464113 / 500000000) := by
  have h := checkLog_sound (w := (431517529 / 124568482471)) (n := 12)
    (lo := (277129 / 40000000)) (hi := (3464113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62068482471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62068482471) = 1/(62068482471 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2093 : Bounds (-3464113 / 500000000) (-277129 / 40000000) (Real.log (62068482471 / 62500000000)) := by
  have h := reflection_log_2093_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2094_neg : (6892127 / 1000000000) ≤ -Real.log (62070723039 / 62500000000) ∧
    -Real.log (62070723039 / 62500000000) ≤ (215379 / 31250000) := by
  have h := checkLog_sound (w := (429276961 / 124570723039)) (n := 12)
    (lo := (6892127 / 1000000000)) (hi := (215379 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62070723039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62070723039) = 1/(62070723039 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2094 : Bounds (-215379 / 31250000) (-6892127 / 1000000000) (Real.log (62070723039 / 62500000000)) := by
  have h := reflection_log_2094_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2095_neg : (166133057 / 1000000000) ≤ -Real.log (500000000000 / 590365097849) ∧
    -Real.log (500000000000 / 590365097849) ≤ (83066529 / 500000000) := by
  have h := checkLog_sound (w := (90365097849 / 1090365097849)) (n := 12)
    (lo := (166133057 / 1000000000)) (hi := (83066529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590365097849 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590365097849 / 500000000000) = 1/(500000000000 / 590365097849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2095 : Bounds (166133057 / 1000000000) (83066529 / 500000000) (Real.log (590365097849 / 500000000000)) := by
  have h := reflection_log_2095_neg
  have he : Real.log (590365097849 / 500000000000) = -Real.log (500000000000 / 590365097849) := by
    rw [show ((590365097849 / 500000000000) : ℝ) = ((500000000000 / 590365097849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2096_neg : (41642013 / 250000000) ≤ -Real.log (125000000000 / 147655489973) ∧
    -Real.log (125000000000 / 147655489973) ≤ (166568053 / 1000000000) := by
  have h := checkLog_sound (w := (22655489973 / 272655489973)) (n := 12)
    (lo := (41642013 / 250000000)) (hi := (166568053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147655489973 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147655489973 / 125000000000) = 1/(125000000000 / 147655489973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2096 : Bounds (41642013 / 250000000) (166568053 / 1000000000) (Real.log (147655489973 / 125000000000)) := by
  have h := reflection_log_2096_neg
  have he : Real.log (147655489973 / 125000000000) = -Real.log (125000000000 / 147655489973) := by
    rw [show ((147655489973 / 125000000000) : ℝ) = ((125000000000 / 147655489973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2097_neg : (166625121 / 500000000) ≤ -Real.log (500000000000 / 697748233321) ∧
    -Real.log (500000000000 / 697748233321) ≤ (333250243 / 1000000000) := by
  have h := checkLog_sound (w := (197748233321 / 1197748233321)) (n := 12)
    (lo := (166625121 / 500000000)) (hi := (333250243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697748233321 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697748233321 / 500000000000) = 1/(500000000000 / 697748233321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2097 : Bounds (166625121 / 500000000) (333250243 / 1000000000) (Real.log (697748233321 / 500000000000)) := by
  have h := reflection_log_2097_neg
  have he : Real.log (697748233321 / 500000000000) = -Real.log (500000000000 / 697748233321) := by
    rw [show ((697748233321 / 500000000000) : ℝ) = ((500000000000 / 697748233321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2098_neg : (333455849 / 1000000000) ≤ -Real.log (50000000000 / 69789171059) ∧
    -Real.log (50000000000 / 69789171059) ≤ (6669117 / 20000000) := by
  have h := checkLog_sound (w := (19789171059 / 119789171059)) (n := 12)
    (lo := (333455849 / 1000000000)) (hi := (6669117 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69789171059 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69789171059 / 50000000000) = 1/(50000000000 / 69789171059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2098 : Bounds (333455849 / 1000000000) (6669117 / 20000000) (Real.log (69789171059 / 50000000000)) := by
  have h := reflection_log_2098_neg
  have he : Real.log (69789171059 / 50000000000) = -Real.log (50000000000 / 69789171059) := by
    rw [show ((69789171059 / 50000000000) : ℝ) = ((50000000000 / 69789171059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2099_neg : (38244641 / 250000000) ≤ -Real.log (10000 / 11653) ∧
    -Real.log (10000 / 11653) ≤ (30595713 / 200000000) := by
  have h := checkLog_sound (w := (1653 / 21653)) (n := 12)
    (lo := (38244641 / 250000000)) (hi := (30595713 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11653 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11653 / 10000) = 1/(10000 / 11653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2099 : Bounds (38244641 / 250000000) (30595713 / 200000000) (Real.log (11653 / 10000)) := by
  have h := reflection_log_2099_neg
  have he : Real.log (11653 / 10000) = -Real.log (10000 / 11653) := by
    rw [show ((11653 / 10000) : ℝ) = ((10000 / 11653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2100_neg : (1806829 / 10000000) ≤ -Real.log (8347 / 10000) ∧
    -Real.log (8347 / 10000) ≤ (180682901 / 1000000000) := by
  have h := checkLog_sound (w := (1653 / 18347)) (n := 12)
    (lo := (1806829 / 10000000)) (hi := (180682901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8347) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8347) = 1/(8347 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2100 : Bounds (-180682901 / 1000000000) (-1806829 / 10000000) (Real.log (8347 / 10000)) := by
  have h := reflection_log_2100_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2101_neg : (82643 / 500000000) ≤ -Real.log (10000000 / 10001653) ∧
    -Real.log (10000000 / 10001653) ≤ (165287 / 1000000000) := by
  have h := checkLog_sound (w := (1653 / 20001653)) (n := 12)
    (lo := (82643 / 500000000)) (hi := (165287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001653 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001653 / 10000000) = 1/(10000000 / 10001653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2101 : Bounds (82643 / 500000000) (165287 / 1000000000) (Real.log (10001653 / 10000000)) := by
  have h := reflection_log_2101_neg
  have he : Real.log (10001653 / 10000000) = -Real.log (10000000 / 10001653) := by
    rw [show ((10001653 / 10000000) : ℝ) = ((10000000 / 10001653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2102_neg : (165313 / 1000000000) ≤ -Real.log (9998347 / 10000000) ∧
    -Real.log (9998347 / 10000000) ≤ (82657 / 500000000) := by
  have h := checkLog_sound (w := (1653 / 19998347)) (n := 12)
    (lo := (165313 / 1000000000)) (hi := (82657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998347) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998347) = 1/(9998347 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2102 : Bounds (-82657 / 500000000) (-165313 / 1000000000) (Real.log (9998347 / 10000000)) := by
  have h := reflection_log_2102_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2103_neg : (1991689 / 25000000) ≤ -Real.log (1000000 / 1082927) ∧
    -Real.log (1000000 / 1082927) ≤ (79667561 / 1000000000) := by
  have h := checkLog_sound (w := (82927 / 2082927)) (n := 12)
    (lo := (1991689 / 25000000)) (hi := (79667561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082927 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082927 / 1000000) = 1/(1000000 / 1082927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2103 : Bounds (1991689 / 25000000) (79667561 / 1000000000) (Real.log (1082927 / 1000000)) := by
  have h := reflection_log_2103_neg
  have he : Real.log (1082927 / 1000000) = -Real.log (1000000 / 1082927) := by
    rw [show ((1082927 / 1000000) : ℝ) = ((1000000 / 1082927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2104_neg : (43284101 / 500000000) ≤ -Real.log (917073 / 1000000) ∧
    -Real.log (917073 / 1000000) ≤ (86568203 / 1000000000) := by
  have h := checkLog_sound (w := (82927 / 1917073)) (n := 12)
    (lo := (43284101 / 500000000)) (hi := (86568203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917073) = 1/(917073 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2104 : Bounds (-86568203 / 1000000000) (-43284101 / 500000000) (Real.log (917073 / 1000000)) := by
  have h := reflection_log_2104_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2105_neg : (79866999 / 1000000000) ≤ -Real.log (1000000 / 1083143) ∧
    -Real.log (1000000 / 1083143) ≤ (79867 / 1000000) := by
  have h := checkLog_sound (w := (83143 / 2083143)) (n := 12)
    (lo := (79866999 / 1000000000)) (hi := (79867 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083143 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083143 / 1000000) = 1/(1000000 / 1083143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2105 : Bounds (79866999 / 1000000000) (79867 / 1000000) (Real.log (1083143 / 1000000)) := by
  have h := reflection_log_2105_neg
  have he : Real.log (1083143 / 1000000) = -Real.log (1000000 / 1083143) := by
    rw [show ((1083143 / 1000000) : ℝ) = ((1000000 / 1083143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2106_neg : (43401881 / 500000000) ≤ -Real.log (916857 / 1000000) ∧
    -Real.log (916857 / 1000000) ≤ (86803763 / 1000000000) := by
  have h := checkLog_sound (w := (83143 / 1916857)) (n := 12)
    (lo := (43401881 / 500000000)) (hi := (86803763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916857) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916857) = 1/(916857 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2106 : Bounds (-86803763 / 1000000000) (-43401881 / 500000000) (Real.log (916857 / 1000000)) := by
  have h := reflection_log_2106_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2107_neg : (3468381 / 500000000) ≤ -Real.log (993087241551 / 1000000000000) ∧
    -Real.log (993087241551 / 1000000000000) ≤ (6936763 / 1000000000) := by
  have h := checkLog_sound (w := (6912758449 / 1993087241551)) (n := 12)
    (lo := (3468381 / 500000000)) (hi := (6936763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993087241551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993087241551) = 1/(993087241551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2107 : Bounds (-6936763 / 1000000000) (-3468381 / 500000000) (Real.log (993087241551 / 1000000000000)) := by
  have h := reflection_log_2107_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2108_neg : (3450321 / 500000000) ≤ -Real.log (993123112671 / 1000000000000) ∧
    -Real.log (993123112671 / 1000000000000) ≤ (6900643 / 1000000000) := by
  have h := checkLog_sound (w := (6876887329 / 1993123112671)) (n := 12)
    (lo := (3450321 / 500000000)) (hi := (6900643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993123112671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993123112671) = 1/(993123112671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2108 : Bounds (-6900643 / 1000000000) (-3450321 / 500000000) (Real.log (993123112671 / 1000000000000)) := by
  have h := reflection_log_2108_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2109_neg : (83117881 / 500000000) ≤ -Real.log (500000000000 / 590425734919) ∧
    -Real.log (500000000000 / 590425734919) ≤ (166235763 / 1000000000) := by
  have h := checkLog_sound (w := (90425734919 / 1090425734919)) (n := 12)
    (lo := (83117881 / 500000000)) (hi := (166235763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590425734919 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590425734919 / 500000000000) = 1/(500000000000 / 590425734919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2109 : Bounds (83117881 / 500000000) (166235763 / 1000000000) (Real.log (590425734919 / 500000000000)) := by
  have h := reflection_log_2109_neg
  have he : Real.log (590425734919 / 500000000000) = -Real.log (500000000000 / 590425734919) := by
    rw [show ((590425734919 / 500000000000) : ℝ) = ((500000000000 / 590425734919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2110_neg : (83335381 / 500000000) ≤ -Real.log (100000000000 / 118136525107) ∧
    -Real.log (100000000000 / 118136525107) ≤ (166670763 / 1000000000) := by
  have h := checkLog_sound (w := (18136525107 / 218136525107)) (n := 12)
    (lo := (83335381 / 500000000)) (hi := (166670763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118136525107 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118136525107 / 100000000000) = 1/(100000000000 / 118136525107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2110 : Bounds (83335381 / 500000000) (166670763 / 1000000000) (Real.log (118136525107 / 100000000000)) := by
  have h := reflection_log_2110_neg
  have he : Real.log (118136525107 / 100000000000) = -Real.log (100000000000 / 118136525107) := by
    rw [show ((118136525107 / 100000000000) : ℝ) = ((100000000000 / 118136525107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2111_neg : (333455849 / 1000000000) ≤ -Real.log (500000000000 / 697891710589) ∧
    -Real.log (500000000000 / 697891710589) ≤ (6669117 / 20000000) := by
  have h := checkLog_sound (w := (197891710589 / 1197891710589)) (n := 12)
    (lo := (333455849 / 1000000000)) (hi := (6669117 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697891710589 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697891710589 / 500000000000) = 1/(500000000000 / 697891710589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2111 : Bounds (333455849 / 1000000000) (6669117 / 20000000) (Real.log (697891710589 / 500000000000)) := by
  have h := reflection_log_2111_neg
  have he : Real.log (697891710589 / 500000000000) = -Real.log (500000000000 / 697891710589) := by
    rw [show ((697891710589 / 500000000000) : ℝ) = ((500000000000 / 697891710589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
