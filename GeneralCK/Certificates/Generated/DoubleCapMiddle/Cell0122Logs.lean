import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0122
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

theorem reflection_log_1_neg : (19672107 / 62500000) ≤ -Real.log (2560 / 3507) ∧
    -Real.log (2560 / 3507) ≤ (314753713 / 1000000000) := by
  have h := checkLog_sound (w := (947 / 6067)) (n := 12)
    (lo := (19672107 / 62500000)) (hi := (314753713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3507 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3507 / 2560) = 1/(2560 / 3507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (19672107 / 62500000) (314753713 / 1000000000) (Real.log (3507 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3507 / 2560) = -Real.log (2560 / 3507) := by
    rw [show ((3507 / 2560) : ℝ) = ((2560 / 3507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (461911459 / 1000000000) ≤ -Real.log (1613 / 2560) ∧
    -Real.log (1613 / 2560) ≤ (23095573 / 50000000) := by
  have h := checkLog_sound (w := (947 / 4173)) (n := 12)
    (lo := (461911459 / 1000000000)) (hi := (23095573 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1613) = 1/(1613 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-23095573 / 50000000) (-461911459 / 1000000000) (Real.log (1613 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (156948957 / 500000000) ≤ -Real.log (160 / 219) ∧
    -Real.log (160 / 219) ≤ (62779583 / 200000000) := by
  have h := checkLog_sound (w := (59 / 379)) (n := 12)
    (lo := (156948957 / 500000000)) (hi := (62779583 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219 / 160) = 1/(160 / 219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (156948957 / 500000000) (62779583 / 200000000) (Real.log (219 / 160)) := by
  have h := reflection_log_3_neg
  have he : Real.log (219 / 160) = -Real.log (160 / 219) := by
    rw [show ((219 / 160) : ℝ) = ((160 / 219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (230026649 / 500000000) ≤ -Real.log (101 / 160) ∧
    -Real.log (101 / 160) ≤ (460053299 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 261)) (n := 12)
    (lo := (230026649 / 500000000)) (hi := (460053299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 101) = 1/(101 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-460053299 / 1000000000) (-230026649 / 500000000) (Real.log (101 / 160)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (55379531 / 100000000) ≤ -Real.log (1280 / 2227) ∧
    -Real.log (1280 / 2227) ≤ (553795311 / 1000000000) := by
  have h := checkLog_sound (w := (947 / 3507)) (n := 12)
    (lo := (55379531 / 100000000)) (hi := (553795311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2227 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2227 / 1280) = 1/(1280 / 2227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (55379531 / 100000000) (553795311 / 1000000000) (Real.log (2227 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2227 / 1280) = -Real.log (1280 / 2227) := by
    rw [show ((2227 / 1280) : ℝ) = ((1280 / 2227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (673236433 / 500000000) ≤ -Real.log (333 / 1280) ∧
    -Real.log (333 / 1280) ≤ (336618217 / 250000000) := by
  have h := checkLog_sound (w := (307 / 973)) (n := 12)
    (lo := (326662843 / 500000000)) (hi := (653325687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 333) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 333) = 1/(333 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-336618217 / 250000000) (-673236433 / 500000000) (Real.log (333 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (276223649 / 500000000) ≤ -Real.log (80 / 139) ∧
    -Real.log (80 / 139) ≤ (552447299 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 219)) (n := 12)
    (lo := (276223649 / 500000000)) (hi := (552447299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139 / 80) = 1/(80 / 139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (276223649 / 500000000) (552447299 / 1000000000) (Real.log (139 / 80)) := by
  have h := reflection_log_7_neg
  have he : Real.log (139 / 80) = -Real.log (80 / 139) := by
    rw [show ((139 / 80) : ℝ) = ((80 / 139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (334376049 / 250000000) ≤ -Real.log (21 / 80) ∧
    -Real.log (21 / 80) ≤ (668752099 / 500000000) := by
  have h := checkLog_sound (w := (19 / 61)) (n := 12)
    (lo := (80544627 / 125000000)) (hi := (644357017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 21) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 21) = 1/(21 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-668752099 / 500000000) (-334376049 / 250000000) (Real.log (21 / 80)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (429974289 / 1000000000) ≤ -Real.log (500000 / 768609) ∧
    -Real.log (500000 / 768609) ≤ (42997429 / 100000000) := by
  have h := checkLog_sound (w := (268609 / 1268609)) (n := 12)
    (lo := (429974289 / 1000000000)) (hi := (42997429 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((768609 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(768609 / 500000) = 1/(500000 / 768609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (429974289 / 1000000000) (42997429 / 100000000) (Real.log (768609 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (768609 / 500000) = -Real.log (500000 / 768609) := by
    rw [show ((768609 / 500000) : ℝ) = ((500000 / 768609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (770499177 / 1000000000) ≤ -Real.log (231391 / 500000) ∧
    -Real.log (231391 / 500000) ≤ (770499179 / 1000000000) := by
  have h := checkLog_sound (w := (18609 / 481391)) (n := 12)
    (lo := (77351997 / 1000000000)) (hi := (38675999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 231391) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 231391) = 1/(231391 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-770499179 / 1000000000) (-770499177 / 1000000000) (Real.log (231391 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (431175089 / 1000000000) ≤ -Real.log (200000 / 307813) ∧
    -Real.log (200000 / 307813) ≤ (43117509 / 100000000) := by
  have h := checkLog_sound (w := (107813 / 507813)) (n := 12)
    (lo := (431175089 / 1000000000)) (hi := (43117509 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307813 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307813 / 200000) = 1/(200000 / 307813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (431175089 / 1000000000) (43117509 / 100000000) (Real.log (307813 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (307813 / 200000) = -Real.log (200000 / 307813) := by
    rw [show ((307813 / 200000) : ℝ) = ((200000 / 307813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (774498243 / 1000000000) ≤ -Real.log (92187 / 200000) ∧
    -Real.log (92187 / 200000) ≤ (154899649 / 200000000) := by
  have h := checkLog_sound (w := (7813 / 192187)) (n := 12)
    (lo := (81351063 / 1000000000)) (hi := (10168883 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 92187) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 92187) = 1/(92187 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-154899649 / 200000000) (-774498243 / 1000000000) (Real.log (92187 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (345487901 / 1000000000) ≤ -Real.log (1000000 / 1412679) ∧
    -Real.log (1000000 / 1412679) ≤ (172743951 / 500000000) := by
  have h := checkLog_sound (w := (412679 / 2412679)) (n := 12)
    (lo := (345487901 / 1000000000)) (hi := (172743951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1412679 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1412679 / 1000000) = 1/(1000000 / 1412679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (345487901 / 1000000000) (172743951 / 500000000) (Real.log (1412679 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1412679 / 1000000) = -Real.log (1000000 / 1412679) := by
    rw [show ((1412679 / 1000000) : ℝ) = ((1000000 / 1412679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (6652297 / 12500000) ≤ -Real.log (587321 / 1000000) ∧
    -Real.log (587321 / 1000000) ≤ (532183761 / 1000000000) := by
  have h := checkLog_sound (w := (412679 / 1587321)) (n := 12)
    (lo := (6652297 / 12500000)) (hi := (532183761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 587321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 587321) = 1/(587321 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-532183761 / 1000000000) (-6652297 / 12500000) (Real.log (587321 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (43333139 / 125000000) ≤ -Real.log (1000000 / 1414343) ∧
    -Real.log (1000000 / 1414343) ≤ (346665113 / 1000000000) := by
  have h := checkLog_sound (w := (414343 / 2414343)) (n := 12)
    (lo := (43333139 / 125000000)) (hi := (346665113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1414343 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1414343 / 1000000) = 1/(1000000 / 1414343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (43333139 / 125000000) (346665113 / 1000000000) (Real.log (1414343 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1414343 / 1000000) = -Real.log (1000000 / 1414343) := by
    rw [show ((1414343 / 1000000) : ℝ) = ((1000000 / 1414343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (107004197 / 200000000) ≤ -Real.log (585657 / 1000000) ∧
    -Real.log (585657 / 1000000) ≤ (267510493 / 500000000) := by
  have h := checkLog_sound (w := (414343 / 1585657)) (n := 12)
    (lo := (107004197 / 200000000)) (hi := (267510493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 585657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 585657) = 1/(585657 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-267510493 / 500000000) (-107004197 / 200000000) (Real.log (585657 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (600236733 / 500000000) ≤ -Real.log (500000000000 / 1660844630949) ∧
    -Real.log (500000000000 / 1660844630949) ≤ (300118367 / 250000000) := by
  have h := checkLog_sound (w := (660844630949 / 2660844630949)) (n := 12)
    (lo := (253663143 / 500000000)) (hi := (507326287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1660844630949 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1660844630949 / 1000000000000) = 1/(500000000000 / 1660844630949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (600236733 / 500000000) (300118367 / 250000000) (Real.log (1660844630949 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1660844630949 / 500000000000) = -Real.log (500000000000 / 1660844630949) := by
    rw [show ((1660844630949 / 500000000000) : ℝ) = ((500000000000 / 1660844630949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (301418333 / 250000000) ≤ -Real.log (250000000000 / 834751646111) ∧
    -Real.log (250000000000 / 834751646111) ≤ (602836667 / 500000000) := by
  have h := checkLog_sound (w := (334751646111 / 1334751646111)) (n := 12)
    (lo := (64065769 / 125000000)) (hi := (512526153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((834751646111 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(834751646111 / 500000000000) = 1/(250000000000 / 834751646111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (301418333 / 250000000) (602836667 / 500000000) (Real.log (834751646111 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (834751646111 / 250000000000) = -Real.log (250000000000 / 834751646111) := by
    rw [show ((834751646111 / 250000000000) : ℝ) = ((250000000000 / 834751646111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (877671661 / 1000000000) ≤ -Real.log (100000000000 / 240529284667) ∧
    -Real.log (100000000000 / 240529284667) ≤ (877671663 / 1000000000) := by
  have h := checkLog_sound (w := (40529284667 / 440529284667)) (n := 12)
    (lo := (184524481 / 1000000000)) (hi := (92262241 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((240529284667 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(240529284667 / 200000000000) = 1/(100000000000 / 240529284667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (877671661 / 1000000000) (877671663 / 1000000000) (Real.log (240529284667 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (240529284667 / 100000000000) = -Real.log (100000000000 / 240529284667) := by
    rw [show ((240529284667 / 100000000000) : ℝ) = ((100000000000 / 240529284667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (55105381 / 62500000) ≤ -Real.log (500000000000 / 1207484073443) ∧
    -Real.log (500000000000 / 1207484073443) ≤ (440843049 / 500000000) := by
  have h := checkLog_sound (w := (207484073443 / 2207484073443)) (n := 12)
    (lo := (47134729 / 250000000)) (hi := (188538917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1207484073443 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1207484073443 / 1000000000000) = 1/(500000000000 / 1207484073443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (55105381 / 62500000) (440843049 / 500000000) (Real.log (1207484073443 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1207484073443 / 500000000000) = -Real.log (500000000000 / 1207484073443) := by
    rw [show ((1207484073443 / 500000000000) : ℝ) = ((500000000000 / 1207484073443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0122
