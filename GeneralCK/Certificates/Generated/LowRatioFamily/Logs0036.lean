import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2304_neg : (438733 / 62500000) ≤ -Real.log (993004852231 / 1000000000000) ∧
    -Real.log (993004852231 / 1000000000000) ≤ (7019729 / 1000000000) := by
  have h := checkLog_sound (w := (6995147769 / 1993004852231)) (n := 12)
    (lo := (438733 / 62500000)) (hi := (7019729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993004852231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993004852231) = 1/(993004852231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2304 : Bounds (-7019729 / 1000000000) (-438733 / 62500000) (Real.log (993004852231 / 1000000000000)) := by
  have h := reflection_log_2304_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2305_neg : (2095821 / 12500000) ≤ -Real.log (62500000000 / 73908824887) ∧
    -Real.log (62500000000 / 73908824887) ≤ (167665681 / 1000000000) := by
  have h := checkLog_sound (w := (11408824887 / 136408824887)) (n := 12)
    (lo := (2095821 / 12500000)) (hi := (167665681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73908824887 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73908824887 / 62500000000) = 1/(62500000000 / 73908824887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2305 : Bounds (2095821 / 12500000) (167665681 / 1000000000) (Real.log (73908824887 / 62500000000)) := by
  have h := reflection_log_2305_neg
  have he : Real.log (73908824887 / 62500000000) = -Real.log (62500000000 / 73908824887) := by
    rw [show ((73908824887 / 62500000000) : ℝ) = ((62500000000 / 73908824887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2306_neg : (4202619 / 25000000) ≤ -Real.log (31250000000 / 36970641929) ∧
    -Real.log (31250000000 / 36970641929) ≤ (168104761 / 1000000000) := by
  have h := checkLog_sound (w := (5720641929 / 68220641929)) (n := 12)
    (lo := (4202619 / 25000000)) (hi := (168104761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36970641929 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36970641929 / 31250000000) = 1/(31250000000 / 36970641929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2306 : Bounds (4202619 / 25000000) (168104761 / 1000000000) (Real.log (36970641929 / 31250000000)) := by
  have h := reflection_log_2306_neg
  have he : Real.log (36970641929 / 31250000000) = -Real.log (31250000000 / 36970641929) := by
    rw [show ((36970641929 / 31250000000) : ℝ) = ((31250000000 / 36970641929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2307_neg : (67267019 / 200000000) ≤ -Real.log (500000000000 / 699904007679) ∧
    -Real.log (500000000000 / 699904007679) ≤ (42041887 / 125000000) := by
  have h := checkLog_sound (w := (199904007679 / 1199904007679)) (n := 12)
    (lo := (67267019 / 200000000)) (hi := (42041887 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699904007679 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699904007679 / 500000000000) = 1/(500000000000 / 699904007679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2307 : Bounds (67267019 / 200000000) (42041887 / 125000000) (Real.log (699904007679 / 500000000000)) := by
  have h := reflection_log_2307_neg
  have he : Real.log (699904007679 / 500000000000) = -Real.log (500000000000 / 699904007679) := by
    rw [show ((699904007679 / 500000000000) : ℝ) = ((500000000000 / 699904007679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2308_neg : (42067601 / 125000000) ≤ -Real.log (500000000000 / 700048001921) ∧
    -Real.log (500000000000 / 700048001921) ≤ (336540809 / 1000000000) := by
  have h := checkLog_sound (w := (200048001921 / 1200048001921)) (n := 12)
    (lo := (42067601 / 125000000)) (hi := (336540809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((700048001921 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(700048001921 / 500000000000) = 1/(500000000000 / 700048001921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2308 : Bounds (42067601 / 125000000) (336540809 / 1000000000) (Real.log (700048001921 / 500000000000)) := by
  have h := reflection_log_2308_neg
  have he : Real.log (700048001921 / 500000000000) = -Real.log (500000000000 / 700048001921) := by
    rw [show ((700048001921 / 500000000000) : ℝ) = ((500000000000 / 700048001921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2309_neg : (154264959 / 1000000000) ≤ -Real.log (2500 / 2917) ∧
    -Real.log (2500 / 2917) ≤ (241039 / 1562500) := by
  have h := checkLog_sound (w := (417 / 5417)) (n := 12)
    (lo := (154264959 / 1000000000)) (hi := (241039 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2917 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2917 / 2500) = 1/(2500 / 2917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2309 : Bounds (154264959 / 1000000000) (241039 / 1562500) (Real.log (2917 / 2500)) := by
  have h := reflection_log_2309_neg
  have he : Real.log (2917 / 2500) = -Real.log (2500 / 2917) := by
    rw [show ((2917 / 2500) : ℝ) = ((2500 / 2917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2310_neg : (182481569 / 1000000000) ≤ -Real.log (2083 / 2500) ∧
    -Real.log (2083 / 2500) ≤ (18248157 / 100000000) := by
  have h := checkLog_sound (w := (417 / 4583)) (n := 12)
    (lo := (182481569 / 1000000000)) (hi := (18248157 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2083) = 1/(2083 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2310 : Bounds (-18248157 / 100000000) (-182481569 / 1000000000) (Real.log (2083 / 2500)) := by
  have h := reflection_log_2310_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2311_neg : (83393 / 500000000) ≤ -Real.log (2500000 / 2500417) ∧
    -Real.log (2500000 / 2500417) ≤ (166787 / 1000000000) := by
  have h := checkLog_sound (w := (417 / 5000417)) (n := 12)
    (lo := (83393 / 500000000)) (hi := (166787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500417 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500417 / 2500000) = 1/(2500000 / 2500417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2311 : Bounds (83393 / 500000000) (166787 / 1000000000) (Real.log (2500417 / 2500000)) := by
  have h := reflection_log_2311_neg
  have he : Real.log (2500417 / 2500000) = -Real.log (2500000 / 2500417) := by
    rw [show ((2500417 / 2500000) : ℝ) = ((2500000 / 2500417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2312_neg : (166813 / 1000000000) ≤ -Real.log (2499583 / 2500000) ∧
    -Real.log (2499583 / 2500000) ≤ (83407 / 500000000) := by
  have h := checkLog_sound (w := (417 / 4999583)) (n := 12)
    (lo := (166813 / 1000000000)) (hi := (83407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499583) = 1/(2499583 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2312 : Bounds (-83407 / 500000000) (-166813 / 1000000000) (Real.log (2499583 / 2500000)) := by
  have h := reflection_log_2312_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2313_neg : (40185019 / 500000000) ≤ -Real.log (125000 / 135461) ∧
    -Real.log (125000 / 135461) ≤ (80370039 / 1000000000) := by
  have h := checkLog_sound (w := (10461 / 260461)) (n := 12)
    (lo := (40185019 / 500000000)) (hi := (80370039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135461 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135461 / 125000) = 1/(125000 / 135461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2313 : Bounds (40185019 / 500000000) (80370039 / 1000000000) (Real.log (135461 / 125000)) := by
  have h := reflection_log_2313_neg
  have he : Real.log (135461 / 125000) = -Real.log (125000 / 135461) := by
    rw [show ((135461 / 125000) : ℝ) = ((125000 / 135461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2314_neg : (2184959 / 25000000) ≤ -Real.log (114539 / 125000) ∧
    -Real.log (114539 / 125000) ≤ (87398361 / 1000000000) := by
  have h := checkLog_sound (w := (10461 / 239539)) (n := 12)
    (lo := (2184959 / 25000000)) (hi := (87398361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 114539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 114539) = 1/(114539 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2314 : Bounds (-87398361 / 1000000000) (-2184959 / 25000000) (Real.log (114539 / 125000)) := by
  have h := reflection_log_2314_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2315_neg : (4028513 / 50000000) ≤ -Real.log (200000 / 216781) ∧
    -Real.log (200000 / 216781) ≤ (80570261 / 1000000000) := by
  have h := checkLog_sound (w := (16781 / 416781)) (n := 12)
    (lo := (4028513 / 50000000)) (hi := (80570261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216781 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216781 / 200000) = 1/(200000 / 216781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2315 : Bounds (4028513 / 50000000) (80570261 / 1000000000) (Real.log (216781 / 200000)) := by
  have h := reflection_log_2315_neg
  have he : Real.log (216781 / 200000) = -Real.log (200000 / 216781) := by
    rw [show ((216781 / 200000) : ℝ) = ((200000 / 216781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2316_neg : (87635207 / 1000000000) ≤ -Real.log (183219 / 200000) ∧
    -Real.log (183219 / 200000) ≤ (10954401 / 125000000) := by
  have h := checkLog_sound (w := (16781 / 383219)) (n := 12)
    (lo := (87635207 / 1000000000)) (hi := (10954401 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183219) = 1/(183219 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2316 : Bounds (-10954401 / 125000000) (-87635207 / 1000000000) (Real.log (183219 / 200000)) := by
  have h := reflection_log_2316_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2317_neg : (7064947 / 1000000000) ≤ -Real.log (39718398039 / 40000000000) ∧
    -Real.log (39718398039 / 40000000000) ≤ (1766237 / 250000000) := by
  have h := checkLog_sound (w := (281601961 / 79718398039)) (n := 12)
    (lo := (7064947 / 1000000000)) (hi := (1766237 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39718398039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39718398039) = 1/(39718398039 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2317 : Bounds (-1766237 / 250000000) (-7064947 / 1000000000) (Real.log (39718398039 / 40000000000)) := by
  have h := reflection_log_2317_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2318_neg : (3514161 / 500000000) ≤ -Real.log (15515567479 / 15625000000) ∧
    -Real.log (15515567479 / 15625000000) ≤ (7028323 / 1000000000) := by
  have h := checkLog_sound (w := (109432521 / 31140567479)) (n := 12)
    (lo := (3514161 / 500000000)) (hi := (7028323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15515567479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15515567479) = 1/(15515567479 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2318 : Bounds (-7028323 / 1000000000) (-3514161 / 500000000) (Real.log (15515567479 / 15625000000)) := by
  have h := reflection_log_2318_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2319_neg : (167768399 / 1000000000) ≤ -Real.log (125000000000 / 147832834231) ∧
    -Real.log (125000000000 / 147832834231) ≤ (419421 / 2500000) := by
  have h := checkLog_sound (w := (22832834231 / 272832834231)) (n := 12)
    (lo := (167768399 / 1000000000)) (hi := (419421 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147832834231 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147832834231 / 125000000000) = 1/(125000000000 / 147832834231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2319 : Bounds (167768399 / 1000000000) (419421 / 2500000) (Real.log (147832834231 / 125000000000)) := by
  have h := reflection_log_2319_neg
  have he : Real.log (147832834231 / 125000000000) = -Real.log (125000000000 / 147832834231) := by
    rw [show ((147832834231 / 125000000000) : ℝ) = ((125000000000 / 147832834231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2320_neg : (42051367 / 250000000) ≤ -Real.log (31250000000 / 36974365377) ∧
    -Real.log (31250000000 / 36974365377) ≤ (168205469 / 1000000000) := by
  have h := checkLog_sound (w := (5724365377 / 68224365377)) (n := 12)
    (lo := (42051367 / 250000000)) (hi := (168205469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36974365377 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36974365377 / 31250000000) = 1/(31250000000 / 36974365377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2320 : Bounds (42051367 / 250000000) (168205469 / 1000000000) (Real.log (36974365377 / 31250000000)) := by
  have h := reflection_log_2320_neg
  have he : Real.log (36974365377 / 31250000000) = -Real.log (31250000000 / 36974365377) := by
    rw [show ((36974365377 / 31250000000) : ℝ) = ((31250000000 / 36974365377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2321_neg : (42067601 / 125000000) ≤ -Real.log (781250000 / 1093825003) ∧
    -Real.log (781250000 / 1093825003) ≤ (336540809 / 1000000000) := by
  have h := checkLog_sound (w := (312575003 / 1875075003)) (n := 12)
    (lo := (42067601 / 125000000)) (hi := (336540809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1093825003 / 781250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1093825003 / 781250000) = 1/(781250000 / 1093825003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2321 : Bounds (42067601 / 125000000) (336540809 / 1000000000) (Real.log (1093825003 / 781250000)) := by
  have h := reflection_log_2321_neg
  have he : Real.log (1093825003 / 781250000) = -Real.log (781250000 / 1093825003) := by
    rw [show ((1093825003 / 781250000) : ℝ) = ((781250000 / 1093825003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2322_neg : (10523329 / 31250000) ≤ -Real.log (20000000000 / 28007681229) ∧
    -Real.log (20000000000 / 28007681229) ≤ (336746529 / 1000000000) := by
  have h := checkLog_sound (w := (8007681229 / 48007681229)) (n := 12)
    (lo := (10523329 / 31250000)) (hi := (336746529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28007681229 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28007681229 / 20000000000) = 1/(20000000000 / 28007681229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2322 : Bounds (10523329 / 31250000) (336746529 / 1000000000) (Real.log (28007681229 / 20000000000)) := by
  have h := reflection_log_2322_neg
  have he : Real.log (28007681229 / 20000000000) = -Real.log (20000000000 / 28007681229) := by
    rw [show ((28007681229 / 20000000000) : ℝ) = ((20000000000 / 28007681229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2323_neg : (154350659 / 1000000000) ≤ -Real.log (10000 / 11669) ∧
    -Real.log (10000 / 11669) ≤ (7717533 / 50000000) := by
  have h := checkLog_sound (w := (1669 / 21669)) (n := 12)
    (lo := (154350659 / 1000000000)) (hi := (7717533 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11669 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11669 / 10000) = 1/(10000 / 11669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2323 : Bounds (154350659 / 1000000000) (7717533 / 50000000) (Real.log (11669 / 10000)) := by
  have h := reflection_log_2323_neg
  have he : Real.log (11669 / 10000) = -Real.log (10000 / 11669) := by
    rw [show ((11669 / 10000) : ℝ) = ((10000 / 11669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2324_neg : (45650399 / 250000000) ≤ -Real.log (8331 / 10000) ∧
    -Real.log (8331 / 10000) ≤ (182601597 / 1000000000) := by
  have h := checkLog_sound (w := (1669 / 18331)) (n := 12)
    (lo := (45650399 / 250000000)) (hi := (182601597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8331) = 1/(8331 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2324 : Bounds (-182601597 / 1000000000) (-45650399 / 250000000) (Real.log (8331 / 10000)) := by
  have h := reflection_log_2324_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2325_neg : (83443 / 500000000) ≤ -Real.log (10000000 / 10001669) ∧
    -Real.log (10000000 / 10001669) ≤ (166887 / 1000000000) := by
  have h := checkLog_sound (w := (1669 / 20001669)) (n := 12)
    (lo := (83443 / 500000000)) (hi := (166887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001669 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001669 / 10000000) = 1/(10000000 / 10001669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2325 : Bounds (83443 / 500000000) (166887 / 1000000000) (Real.log (10001669 / 10000000)) := by
  have h := reflection_log_2325_neg
  have he : Real.log (10001669 / 10000000) = -Real.log (10000000 / 10001669) := by
    rw [show ((10001669 / 10000000) : ℝ) = ((10000000 / 10001669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2326_neg : (166913 / 1000000000) ≤ -Real.log (9998331 / 10000000) ∧
    -Real.log (9998331 / 10000000) ≤ (83457 / 500000000) := by
  have h := checkLog_sound (w := (1669 / 19998331)) (n := 12)
    (lo := (166913 / 1000000000)) (hi := (83457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998331) = 1/(9998331 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2326 : Bounds (-83457 / 500000000) (-166913 / 1000000000) (Real.log (9998331 / 10000000)) := by
  have h := reflection_log_2326_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2327_neg : (5026011 / 62500000) ≤ -Real.log (500000 / 541869) ∧
    -Real.log (500000 / 541869) ≤ (80416177 / 1000000000) := by
  have h := checkLog_sound (w := (41869 / 1041869)) (n := 12)
    (lo := (5026011 / 62500000)) (hi := (80416177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541869 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541869 / 500000) = 1/(500000 / 541869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2327 : Bounds (5026011 / 62500000) (80416177 / 1000000000) (Real.log (541869 / 500000)) := by
  have h := reflection_log_2327_neg
  have he : Real.log (541869 / 500000) = -Real.log (500000 / 541869) := by
    rw [show ((541869 / 500000) : ℝ) = ((500000 / 541869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2328_neg : (87452929 / 1000000000) ≤ -Real.log (458131 / 500000) ∧
    -Real.log (458131 / 500000) ≤ (8745293 / 100000000) := by
  have h := checkLog_sound (w := (41869 / 958131)) (n := 12)
    (lo := (87452929 / 1000000000)) (hi := (8745293 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458131) = 1/(458131 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2328 : Bounds (-8745293 / 100000000) (-87452929 / 1000000000) (Real.log (458131 / 500000)) := by
  have h := reflection_log_2328_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2329_neg : (80617311 / 1000000000) ≤ -Real.log (250000 / 270989) ∧
    -Real.log (250000 / 270989) ≤ (2519291 / 31250000) := by
  have h := checkLog_sound (w := (20989 / 520989)) (n := 12)
    (lo := (80617311 / 1000000000)) (hi := (2519291 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270989 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270989 / 250000) = 1/(250000 / 270989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2329 : Bounds (80617311 / 1000000000) (2519291 / 31250000) (Real.log (270989 / 250000)) := by
  have h := reflection_log_2329_neg
  have he : Real.log (270989 / 250000) = -Real.log (250000 / 270989) := by
    rw [show ((270989 / 250000) : ℝ) = ((250000 / 270989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2330_neg : (137017 / 1562500) ≤ -Real.log (229011 / 250000) ∧
    -Real.log (229011 / 250000) ≤ (87690881 / 1000000000) := by
  have h := checkLog_sound (w := (20989 / 479011)) (n := 12)
    (lo := (137017 / 1562500)) (hi := (87690881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229011) = 1/(229011 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2330 : Bounds (-87690881 / 1000000000) (-137017 / 1562500) (Real.log (229011 / 250000)) := by
  have h := reflection_log_2330_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2331_neg : (221049 / 31250000) ≤ -Real.log (62059461879 / 62500000000) ∧
    -Real.log (62059461879 / 62500000000) ≤ (7073569 / 1000000000) := by
  have h := checkLog_sound (w := (440538121 / 124559461879)) (n := 12)
    (lo := (221049 / 31250000)) (hi := (7073569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62059461879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62059461879) = 1/(62059461879 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2331 : Bounds (-7073569 / 1000000000) (-221049 / 31250000) (Real.log (62059461879 / 62500000000)) := by
  have h := reflection_log_2331_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2332_neg : (439797 / 62500000) ≤ -Real.log (248246986839 / 250000000000) ∧
    -Real.log (248246986839 / 250000000000) ≤ (7036753 / 1000000000) := by
  have h := checkLog_sound (w := (1753013161 / 498246986839)) (n := 12)
    (lo := (439797 / 62500000)) (hi := (7036753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248246986839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248246986839) = 1/(248246986839 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2332 : Bounds (-7036753 / 1000000000) (-439797 / 62500000) (Real.log (248246986839 / 250000000000)) := by
  have h := reflection_log_2332_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2333_neg : (33573821 / 200000000) ≤ -Real.log (250000000000 / 295695445189) ∧
    -Real.log (250000000000 / 295695445189) ≤ (83934553 / 500000000) := by
  have h := checkLog_sound (w := (45695445189 / 545695445189)) (n := 12)
    (lo := (33573821 / 200000000)) (hi := (83934553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295695445189 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295695445189 / 250000000000) = 1/(250000000000 / 295695445189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2333 : Bounds (33573821 / 200000000) (83934553 / 500000000) (Real.log (295695445189 / 250000000000)) := by
  have h := reflection_log_2333_neg
  have he : Real.log (295695445189 / 250000000000) = -Real.log (250000000000 / 295695445189) := by
    rw [show ((295695445189 / 250000000000) : ℝ) = ((250000000000 / 295695445189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2334_neg : (5259631 / 31250000) ≤ -Real.log (500000000000 / 591650619403) ∧
    -Real.log (500000000000 / 591650619403) ≤ (168308193 / 1000000000) := by
  have h := checkLog_sound (w := (91650619403 / 1091650619403)) (n := 12)
    (lo := (5259631 / 31250000)) (hi := (168308193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591650619403 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591650619403 / 500000000000) = 1/(500000000000 / 591650619403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2334 : Bounds (5259631 / 31250000) (168308193 / 1000000000) (Real.log (591650619403 / 500000000000)) := by
  have h := reflection_log_2334_neg
  have he : Real.log (591650619403 / 500000000000) = -Real.log (500000000000 / 591650619403) := by
    rw [show ((591650619403 / 500000000000) : ℝ) = ((500000000000 / 591650619403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2335_neg : (10523329 / 31250000) ≤ -Real.log (125000000000 / 175048007681) ∧
    -Real.log (125000000000 / 175048007681) ≤ (336746529 / 1000000000) := by
  have h := checkLog_sound (w := (50048007681 / 300048007681)) (n := 12)
    (lo := (10523329 / 31250000)) (hi := (336746529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175048007681 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175048007681 / 125000000000) = 1/(125000000000 / 175048007681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2335 : Bounds (10523329 / 31250000) (336746529 / 1000000000) (Real.log (175048007681 / 125000000000)) := by
  have h := reflection_log_2335_neg
  have he : Real.log (175048007681 / 125000000000) = -Real.log (125000000000 / 175048007681) := by
    rw [show ((175048007681 / 125000000000) : ℝ) = ((125000000000 / 175048007681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2336_neg : (67390451 / 200000000) ≤ -Real.log (500000000000 / 700336094107) ∧
    -Real.log (500000000000 / 700336094107) ≤ (5264879 / 15625000) := by
  have h := checkLog_sound (w := (200336094107 / 1200336094107)) (n := 12)
    (lo := (67390451 / 200000000)) (hi := (5264879 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((700336094107 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(700336094107 / 500000000000) = 1/(500000000000 / 700336094107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2336 : Bounds (67390451 / 200000000) (5264879 / 15625000) (Real.log (700336094107 / 500000000000)) := by
  have h := reflection_log_2336_neg
  have he : Real.log (700336094107 / 500000000000) = -Real.log (500000000000 / 700336094107) := by
    rw [show ((700336094107 / 500000000000) : ℝ) = ((500000000000 / 700336094107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2337_neg : (154436353 / 1000000000) ≤ -Real.log (1000 / 1167) ∧
    -Real.log (1000 / 1167) ≤ (77218177 / 500000000) := by
  have h := checkLog_sound (w := (167 / 2167)) (n := 12)
    (lo := (154436353 / 1000000000)) (hi := (77218177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1167 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1167 / 1000) = 1/(1000 / 1167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2337 : Bounds (154436353 / 1000000000) (77218177 / 500000000) (Real.log (1167 / 1000)) := by
  have h := reflection_log_2337_neg
  have he : Real.log (1167 / 1000) = -Real.log (1000 / 1167) := by
    rw [show ((1167 / 1000) : ℝ) = ((1000 / 1167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2338_neg : (45680409 / 250000000) ≤ -Real.log (833 / 1000) ∧
    -Real.log (833 / 1000) ≤ (182721637 / 1000000000) := by
  have h := checkLog_sound (w := (167 / 1833)) (n := 12)
    (lo := (45680409 / 250000000)) (hi := (182721637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 833) = 1/(833 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2338 : Bounds (-182721637 / 1000000000) (-45680409 / 250000000) (Real.log (833 / 1000)) := by
  have h := reflection_log_2338_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2339_neg : (83493 / 500000000) ≤ -Real.log (1000000 / 1000167) ∧
    -Real.log (1000000 / 1000167) ≤ (166987 / 1000000000) := by
  have h := checkLog_sound (w := (167 / 2000167)) (n := 12)
    (lo := (83493 / 500000000)) (hi := (166987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000167 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000167 / 1000000) = 1/(1000000 / 1000167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2339 : Bounds (83493 / 500000000) (166987 / 1000000000) (Real.log (1000167 / 1000000)) := by
  have h := reflection_log_2339_neg
  have he : Real.log (1000167 / 1000000) = -Real.log (1000000 / 1000167) := by
    rw [show ((1000167 / 1000000) : ℝ) = ((1000000 / 1000167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2340_neg : (167013 / 1000000000) ≤ -Real.log (999833 / 1000000) ∧
    -Real.log (999833 / 1000000) ≤ (83507 / 500000000) := by
  have h := checkLog_sound (w := (167 / 1999833)) (n := 12)
    (lo := (167013 / 1000000000)) (hi := (83507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999833) = 1/(999833 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2340 : Bounds (-83507 / 500000000) (-167013 / 1000000000) (Real.log (999833 / 1000000)) := by
  have h := reflection_log_2340_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2341_neg : (40231617 / 500000000) ≤ -Real.log (1000000 / 1083789) ∧
    -Real.log (1000000 / 1083789) ≤ (16092647 / 200000000) := by
  have h := checkLog_sound (w := (83789 / 2083789)) (n := 12)
    (lo := (40231617 / 500000000)) (hi := (16092647 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083789 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083789 / 1000000) = 1/(1000000 / 1083789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2341 : Bounds (40231617 / 500000000) (16092647 / 200000000) (Real.log (1083789 / 1000000)) := by
  have h := reflection_log_2341_neg
  have he : Real.log (1083789 / 1000000) = -Real.log (1000000 / 1083789) := by
    rw [show ((1083789 / 1000000) : ℝ) = ((1000000 / 1083789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2342_neg : (87508591 / 1000000000) ≤ -Real.log (916211 / 1000000) ∧
    -Real.log (916211 / 1000000) ≤ (5469287 / 62500000) := by
  have h := checkLog_sound (w := (83789 / 1916211)) (n := 12)
    (lo := (87508591 / 1000000000)) (hi := (5469287 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916211) = 1/(916211 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2342 : Bounds (-5469287 / 62500000) (-87508591 / 1000000000) (Real.log (916211 / 1000000)) := by
  have h := reflection_log_2342_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2343_neg : (2016609 / 25000000) ≤ -Real.log (1000000 / 1084007) ∧
    -Real.log (1000000 / 1084007) ≤ (80664361 / 1000000000) := by
  have h := checkLog_sound (w := (84007 / 2084007)) (n := 12)
    (lo := (2016609 / 25000000)) (hi := (80664361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084007 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084007 / 1000000) = 1/(1000000 / 1084007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2343 : Bounds (2016609 / 25000000) (80664361 / 1000000000) (Real.log (1084007 / 1000000)) := by
  have h := reflection_log_2343_neg
  have he : Real.log (1084007 / 1000000) = -Real.log (1000000 / 1084007) := by
    rw [show ((1084007 / 1000000) : ℝ) = ((1000000 / 1084007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2344_neg : (21936639 / 250000000) ≤ -Real.log (915993 / 1000000) ∧
    -Real.log (915993 / 1000000) ≤ (87746557 / 1000000000) := by
  have h := checkLog_sound (w := (84007 / 1915993)) (n := 12)
    (lo := (21936639 / 250000000)) (hi := (87746557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915993) = 1/(915993 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2344 : Bounds (-87746557 / 1000000000) (-21936639 / 250000000) (Real.log (915993 / 1000000)) := by
  have h := reflection_log_2344_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2345_neg : (1416439 / 200000000) ≤ -Real.log (992942823951 / 1000000000000) ∧
    -Real.log (992942823951 / 1000000000000) ≤ (1770549 / 250000000) := by
  have h := checkLog_sound (w := (7057176049 / 1992942823951)) (n := 12)
    (lo := (1416439 / 200000000)) (hi := (1770549 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992942823951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992942823951) = 1/(992942823951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2345 : Bounds (-1770549 / 250000000) (-1416439 / 200000000) (Real.log (992942823951 / 1000000000000)) := by
  have h := reflection_log_2345_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2346_neg : (1761339 / 250000000) ≤ -Real.log (992979403479 / 1000000000000) ∧
    -Real.log (992979403479 / 1000000000000) ≤ (7045357 / 1000000000) := by
  have h := checkLog_sound (w := (7020596521 / 1992979403479)) (n := 12)
    (lo := (1761339 / 250000000)) (hi := (7045357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992979403479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992979403479) = 1/(992979403479 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2346 : Bounds (-7045357 / 1000000000) (-1761339 / 250000000) (Real.log (992979403479 / 1000000000000)) := by
  have h := reflection_log_2346_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2347_neg : (83985913 / 500000000) ≤ -Real.log (500000000000 / 591451641597) ∧
    -Real.log (500000000000 / 591451641597) ≤ (167971827 / 1000000000) := by
  have h := checkLog_sound (w := (91451641597 / 1091451641597)) (n := 12)
    (lo := (83985913 / 500000000)) (hi := (167971827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591451641597 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591451641597 / 500000000000) = 1/(500000000000 / 591451641597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2347 : Bounds (83985913 / 500000000) (167971827 / 1000000000) (Real.log (591451641597 / 500000000000)) := by
  have h := reflection_log_2347_neg
  have he : Real.log (591451641597 / 500000000000) = -Real.log (500000000000 / 591451641597) := by
    rw [show ((591451641597 / 500000000000) : ℝ) = ((500000000000 / 591451641597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2348_neg : (42102729 / 250000000) ≤ -Real.log (250000000000 / 295855699771) ∧
    -Real.log (250000000000 / 295855699771) ≤ (168410917 / 1000000000) := by
  have h := checkLog_sound (w := (45855699771 / 545855699771)) (n := 12)
    (lo := (42102729 / 250000000)) (hi := (168410917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295855699771 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295855699771 / 250000000000) = 1/(250000000000 / 295855699771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2348 : Bounds (42102729 / 250000000) (168410917 / 1000000000) (Real.log (295855699771 / 250000000000)) := by
  have h := reflection_log_2348_neg
  have he : Real.log (295855699771 / 250000000000) = -Real.log (250000000000 / 295855699771) := by
    rw [show ((295855699771 / 250000000000) : ℝ) = ((250000000000 / 295855699771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2349_neg : (67390451 / 200000000) ≤ -Real.log (250000000000 / 350168047053) ∧
    -Real.log (250000000000 / 350168047053) ≤ (5264879 / 15625000) := by
  have h := checkLog_sound (w := (100168047053 / 600168047053)) (n := 12)
    (lo := (67390451 / 200000000)) (hi := (5264879 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((350168047053 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(350168047053 / 250000000000) = 1/(250000000000 / 350168047053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2349 : Bounds (67390451 / 200000000) (5264879 / 15625000) (Real.log (350168047053 / 250000000000)) := by
  have h := reflection_log_2349_neg
  have he : Real.log (350168047053 / 250000000000) = -Real.log (250000000000 / 350168047053) := by
    rw [show ((350168047053 / 250000000000) : ℝ) = ((250000000000 / 350168047053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2350_neg : (33715799 / 100000000) ≤ -Real.log (500000000000 / 700480192077) ∧
    -Real.log (500000000000 / 700480192077) ≤ (337157991 / 1000000000) := by
  have h := checkLog_sound (w := (200480192077 / 1200480192077)) (n := 12)
    (lo := (33715799 / 100000000)) (hi := (337157991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((700480192077 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(700480192077 / 500000000000) = 1/(500000000000 / 700480192077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2350 : Bounds (33715799 / 100000000) (337157991 / 1000000000) (Real.log (700480192077 / 500000000000)) := by
  have h := reflection_log_2350_neg
  have he : Real.log (700480192077 / 500000000000) = -Real.log (500000000000 / 700480192077) := by
    rw [show ((700480192077 / 500000000000) : ℝ) = ((500000000000 / 700480192077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2351_neg : (154522039 / 1000000000) ≤ -Real.log (10000 / 11671) ∧
    -Real.log (10000 / 11671) ≤ (3863051 / 25000000) := by
  have h := checkLog_sound (w := (1671 / 21671)) (n := 12)
    (lo := (154522039 / 1000000000)) (hi := (3863051 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11671 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11671 / 10000) = 1/(10000 / 11671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2351 : Bounds (154522039 / 1000000000) (3863051 / 25000000) (Real.log (11671 / 10000)) := by
  have h := reflection_log_2351_neg
  have he : Real.log (11671 / 10000) = -Real.log (10000 / 11671) := by
    rw [show ((11671 / 10000) : ℝ) = ((10000 / 11671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2352_neg : (45710423 / 250000000) ≤ -Real.log (8329 / 10000) ∧
    -Real.log (8329 / 10000) ≤ (182841693 / 1000000000) := by
  have h := checkLog_sound (w := (1671 / 18329)) (n := 12)
    (lo := (45710423 / 250000000)) (hi := (182841693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8329) = 1/(8329 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2352 : Bounds (-182841693 / 1000000000) (-45710423 / 250000000) (Real.log (8329 / 10000)) := by
  have h := reflection_log_2352_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2353_neg : (83543 / 500000000) ≤ -Real.log (10000000 / 10001671) ∧
    -Real.log (10000000 / 10001671) ≤ (167087 / 1000000000) := by
  have h := checkLog_sound (w := (1671 / 20001671)) (n := 12)
    (lo := (83543 / 500000000)) (hi := (167087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001671 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001671 / 10000000) = 1/(10000000 / 10001671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2353 : Bounds (83543 / 500000000) (167087 / 1000000000) (Real.log (10001671 / 10000000)) := by
  have h := reflection_log_2353_neg
  have he : Real.log (10001671 / 10000000) = -Real.log (10000000 / 10001671) := by
    rw [show ((10001671 / 10000000) : ℝ) = ((10000000 / 10001671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2354_neg : (167113 / 1000000000) ≤ -Real.log (9998329 / 10000000) ∧
    -Real.log (9998329 / 10000000) ≤ (83557 / 500000000) := by
  have h := checkLog_sound (w := (1671 / 19998329)) (n := 12)
    (lo := (167113 / 1000000000)) (hi := (83557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998329) = 1/(9998329 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2354 : Bounds (-83557 / 500000000) (-167113 / 1000000000) (Real.log (9998329 / 10000000)) := by
  have h := reflection_log_2354_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2355_neg : (8051029 / 100000000) ≤ -Real.log (3125 / 3387) ∧
    -Real.log (3125 / 3387) ≤ (80510291 / 1000000000) := by
  have h := checkLog_sound (w := (131 / 3256)) (n := 12)
    (lo := (8051029 / 100000000)) (hi := (80510291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3387 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3387 / 3125) = 1/(3125 / 3387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2355 : Bounds (8051029 / 100000000) (80510291 / 1000000000) (Real.log (3387 / 3125)) := by
  have h := reflection_log_2355_neg
  have he : Real.log (3387 / 3125) = -Real.log (3125 / 3387) := by
    rw [show ((3387 / 3125) : ℝ) = ((3125 / 3387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2356_neg : (87564257 / 1000000000) ≤ -Real.log (2863 / 3125) ∧
    -Real.log (2863 / 3125) ≤ (43782129 / 500000000) := by
  have h := checkLog_sound (w := (131 / 2994)) (n := 12)
    (lo := (87564257 / 1000000000)) (hi := (43782129 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2863) = 1/(2863 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2356 : Bounds (-43782129 / 500000000) (-87564257 / 1000000000) (Real.log (2863 / 3125)) := by
  have h := reflection_log_2356_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2357_neg : (80711407 / 1000000000) ≤ -Real.log (500000 / 542029) ∧
    -Real.log (500000 / 542029) ≤ (5044463 / 62500000) := by
  have h := checkLog_sound (w := (42029 / 1042029)) (n := 12)
    (lo := (80711407 / 1000000000)) (hi := (5044463 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542029 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542029 / 500000) = 1/(500000 / 542029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2357 : Bounds (80711407 / 1000000000) (5044463 / 62500000) (Real.log (542029 / 500000)) := by
  have h := reflection_log_2357_neg
  have he : Real.log (542029 / 500000) = -Real.log (500000 / 542029) := by
    rw [show ((542029 / 500000) : ℝ) = ((500000 / 542029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2358_neg : (17560447 / 200000000) ≤ -Real.log (457971 / 500000) ∧
    -Real.log (457971 / 500000) ≤ (21950559 / 250000000) := by
  have h := checkLog_sound (w := (42029 / 957971)) (n := 12)
    (lo := (17560447 / 200000000)) (hi := (21950559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457971) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457971) = 1/(457971 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2358 : Bounds (-21950559 / 250000000) (-17560447 / 200000000) (Real.log (457971 / 500000)) := by
  have h := reflection_log_2358_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2359_neg : (7090827 / 1000000000) ≤ -Real.log (248233563159 / 250000000000) ∧
    -Real.log (248233563159 / 250000000000) ≤ (1772707 / 250000000) := by
  have h := checkLog_sound (w := (1766436841 / 498233563159)) (n := 12)
    (lo := (7090827 / 1000000000)) (hi := (1772707 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248233563159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248233563159) = 1/(248233563159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2359 : Bounds (-1772707 / 250000000) (-7090827 / 1000000000) (Real.log (248233563159 / 250000000000)) := by
  have h := reflection_log_2359_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2360_neg : (3526983 / 500000000) ≤ -Real.log (9696981 / 9765625) ∧
    -Real.log (9696981 / 9765625) ≤ (7053967 / 1000000000) := by
  have h := checkLog_sound (w := (34322 / 9731303)) (n := 12)
    (lo := (3526983 / 500000000)) (hi := (7053967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9765625 / 9696981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9765625 / 9696981) = 1/(9696981 / 9765625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2360 : Bounds (-7053967 / 1000000000) (-3526983 / 500000000) (Real.log (9696981 / 9765625)) := by
  have h := reflection_log_2360_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2361_neg : (168074547 / 1000000000) ≤ -Real.log (25000000000 / 29575619979) ∧
    -Real.log (25000000000 / 29575619979) ≤ (42018637 / 250000000) := by
  have h := checkLog_sound (w := (4575619979 / 54575619979)) (n := 12)
    (lo := (168074547 / 1000000000)) (hi := (42018637 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29575619979 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29575619979 / 25000000000) = 1/(25000000000 / 29575619979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2361 : Bounds (168074547 / 1000000000) (42018637 / 250000000) (Real.log (29575619979 / 25000000000)) := by
  have h := reflection_log_2361_neg
  have he : Real.log (29575619979 / 25000000000) = -Real.log (25000000000 / 29575619979) := by
    rw [show ((29575619979 / 25000000000) : ℝ) = ((25000000000 / 29575619979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2362_neg : (84256821 / 500000000) ≤ -Real.log (500000000000 / 591772186449) ∧
    -Real.log (500000000000 / 591772186449) ≤ (168513643 / 1000000000) := by
  have h := checkLog_sound (w := (91772186449 / 1091772186449)) (n := 12)
    (lo := (84256821 / 500000000)) (hi := (168513643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591772186449 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591772186449 / 500000000000) = 1/(500000000000 / 591772186449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2362 : Bounds (84256821 / 500000000) (168513643 / 1000000000) (Real.log (591772186449 / 500000000000)) := by
  have h := reflection_log_2362_neg
  have he : Real.log (591772186449 / 500000000000) = -Real.log (500000000000 / 591772186449) := by
    rw [show ((591772186449 / 500000000000) : ℝ) = ((500000000000 / 591772186449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2363_neg : (33715799 / 100000000) ≤ -Real.log (125000000000 / 175120048019) ∧
    -Real.log (125000000000 / 175120048019) ≤ (337157991 / 1000000000) := by
  have h := checkLog_sound (w := (50120048019 / 300120048019)) (n := 12)
    (lo := (33715799 / 100000000)) (hi := (337157991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175120048019 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175120048019 / 125000000000) = 1/(125000000000 / 175120048019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2363 : Bounds (33715799 / 100000000) (337157991 / 1000000000) (Real.log (175120048019 / 125000000000)) := by
  have h := reflection_log_2363_neg
  have he : Real.log (175120048019 / 125000000000) = -Real.log (125000000000 / 175120048019) := by
    rw [show ((175120048019 / 125000000000) : ℝ) = ((125000000000 / 175120048019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2364_neg : (337363731 / 1000000000) ≤ -Real.log (500000000000 / 700624324649) ∧
    -Real.log (500000000000 / 700624324649) ≤ (84340933 / 250000000) := by
  have h := checkLog_sound (w := (200624324649 / 1200624324649)) (n := 12)
    (lo := (337363731 / 1000000000)) (hi := (84340933 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((700624324649 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(700624324649 / 500000000000) = 1/(500000000000 / 700624324649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2364 : Bounds (337363731 / 1000000000) (84340933 / 250000000) (Real.log (700624324649 / 500000000000)) := by
  have h := reflection_log_2364_neg
  have he : Real.log (700624324649 / 500000000000) = -Real.log (500000000000 / 700624324649) := by
    rw [show ((700624324649 / 500000000000) : ℝ) = ((500000000000 / 700624324649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2365_neg : (77303859 / 500000000) ≤ -Real.log (1250 / 1459) ∧
    -Real.log (1250 / 1459) ≤ (154607719 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 2709)) (n := 12)
    (lo := (77303859 / 500000000)) (hi := (154607719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1459 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1459 / 1250) = 1/(1250 / 1459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2365 : Bounds (77303859 / 500000000) (154607719 / 1000000000) (Real.log (1459 / 1250)) := by
  have h := reflection_log_2365_neg
  have he : Real.log (1459 / 1250) = -Real.log (1250 / 1459) := by
    rw [show ((1459 / 1250) : ℝ) = ((1250 / 1459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2366_neg : (182961761 / 1000000000) ≤ -Real.log (1041 / 1250) ∧
    -Real.log (1041 / 1250) ≤ (91480881 / 500000000) := by
  have h := checkLog_sound (w := (209 / 2291)) (n := 12)
    (lo := (182961761 / 1000000000)) (hi := (91480881 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1041) = 1/(1041 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2366 : Bounds (-91480881 / 500000000) (-182961761 / 1000000000) (Real.log (1041 / 1250)) := by
  have h := reflection_log_2366_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2367_neg : (83593 / 500000000) ≤ -Real.log (1250000 / 1250209) ∧
    -Real.log (1250000 / 1250209) ≤ (167187 / 1000000000) := by
  have h := checkLog_sound (w := (209 / 2500209)) (n := 12)
    (lo := (83593 / 500000000)) (hi := (167187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250209 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250209 / 1250000) = 1/(1250000 / 1250209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2367 : Bounds (83593 / 500000000) (167187 / 1000000000) (Real.log (1250209 / 1250000)) := by
  have h := reflection_log_2367_neg
  have he : Real.log (1250209 / 1250000) = -Real.log (1250000 / 1250209) := by
    rw [show ((1250209 / 1250000) : ℝ) = ((1250000 / 1250209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
