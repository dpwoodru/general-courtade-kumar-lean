import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0384
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

theorem reflection_log_1_neg : (204056293 / 1000000000) ≤ -Real.log (5120 / 6279) ∧
    -Real.log (5120 / 6279) ≤ (102028147 / 500000000) := by
  have h := checkLog_sound (w := (1159 / 11399)) (n := 12)
    (lo := (204056293 / 1000000000)) (hi := (102028147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6279 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6279 / 5120) = 1/(5120 / 6279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (204056293 / 1000000000) (102028147 / 500000000) (Real.log (6279 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6279 / 5120) = -Real.log (5120 / 6279) := by
    rw [show ((6279 / 5120) : ℝ) = ((5120 / 6279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (100257 / 390625) ≤ -Real.log (3961 / 5120) ∧
    -Real.log (3961 / 5120) ≤ (256657921 / 1000000000) := by
  have h := checkLog_sound (w := (1159 / 9081)) (n := 12)
    (lo := (100257 / 390625)) (hi := (256657921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3961) = 1/(3961 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-256657921 / 1000000000) (-100257 / 390625) (Real.log (3961 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (50954343 / 250000000) ≤ -Real.log (2048 / 2511) ∧
    -Real.log (2048 / 2511) ≤ (203817373 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 4559)) (n := 12)
    (lo := (50954343 / 250000000)) (hi := (203817373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2511 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2511 / 2048) = 1/(2048 / 2511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (50954343 / 250000000) (203817373 / 1000000000) (Real.log (2511 / 2048)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2511 / 2048) = -Real.log (2048 / 2511) := by
    rw [show ((2511 / 2048) : ℝ) = ((2048 / 2511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (256279299 / 1000000000) ≤ -Real.log (1585 / 2048) ∧
    -Real.log (1585 / 2048) ≤ (2562793 / 10000000) := by
  have h := checkLog_sound (w := (463 / 3633)) (n := 12)
    (lo := (256279299 / 1000000000)) (hi := (2562793 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1585) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1585) = 1/(1585 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2562793 / 10000000) (-256279299 / 1000000000) (Real.log (1585 / 2048)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (93361889 / 250000000) ≤ -Real.log (2560 / 3719) ∧
    -Real.log (2560 / 3719) ≤ (373447557 / 1000000000) := by
  have h := checkLog_sound (w := (1159 / 6279)) (n := 12)
    (lo := (93361889 / 250000000)) (hi := (373447557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3719 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3719 / 2560) = 1/(2560 / 3719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (93361889 / 250000000) (373447557 / 1000000000) (Real.log (3719 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3719 / 2560) = -Real.log (2560 / 3719) := by
    rw [show ((3719 / 2560) : ℝ) = ((2560 / 3719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (602820991 / 1000000000) ≤ -Real.log (1401 / 2560) ∧
    -Real.log (1401 / 2560) ≤ (4709539 / 7812500) := by
  have h := checkLog_sound (w := (1159 / 3961)) (n := 12)
    (lo := (602820991 / 1000000000)) (hi := (4709539 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1401) = 1/(1401 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-4709539 / 7812500) (-602820991 / 1000000000) (Real.log (1401 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (18652207 / 50000000) ≤ -Real.log (1024 / 1487) ∧
    -Real.log (1024 / 1487) ≤ (373044141 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 2511)) (n := 12)
    (lo := (18652207 / 50000000)) (hi := (373044141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1487 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1487 / 1024) = 1/(1024 / 1487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (18652207 / 50000000) (373044141 / 1000000000) (Real.log (1487 / 1024)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1487 / 1024) = -Real.log (1024 / 1487) := by
    rw [show ((1487 / 1024) : ℝ) = ((1024 / 1487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (6017509 / 10000000) ≤ -Real.log (561 / 1024) ∧
    -Real.log (561 / 1024) ≤ (601750901 / 1000000000) := by
  have h := checkLog_sound (w := (463 / 1585)) (n := 12)
    (lo := (6017509 / 10000000)) (hi := (601750901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 561) = 1/(561 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-601750901 / 1000000000) (-6017509 / 10000000) (Real.log (561 / 1024)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (139837551 / 500000000) ≤ -Real.log (10000 / 13227) ∧
    -Real.log (10000 / 13227) ≤ (279675103 / 1000000000) := by
  have h := checkLog_sound (w := (3227 / 23227)) (n := 12)
    (lo := (139837551 / 500000000)) (hi := (279675103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13227 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13227 / 10000) = 1/(10000 / 13227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (139837551 / 500000000) (279675103 / 1000000000) (Real.log (13227 / 10000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (13227 / 10000) = -Real.log (10000 / 13227) := by
    rw [show ((13227 / 10000) : ℝ) = ((10000 / 13227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (97410243 / 250000000) ≤ -Real.log (6773 / 10000) ∧
    -Real.log (6773 / 10000) ≤ (389640973 / 1000000000) := by
  have h := checkLog_sound (w := (3227 / 16773)) (n := 12)
    (lo := (97410243 / 250000000)) (hi := (389640973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 6773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 6773) = 1/(6773 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-389640973 / 1000000000) (-97410243 / 250000000) (Real.log (6773 / 10000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (27999863 / 100000000) ≤ -Real.log (125000 / 165391) ∧
    -Real.log (125000 / 165391) ≤ (279998631 / 1000000000) := by
  have h := checkLog_sound (w := (40391 / 290391)) (n := 12)
    (lo := (27999863 / 100000000)) (hi := (279998631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165391 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165391 / 125000) = 1/(125000 / 165391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (27999863 / 100000000) (279998631 / 1000000000) (Real.log (165391 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (165391 / 125000) = -Real.log (125000 / 165391) := by
    rw [show ((165391 / 125000) : ℝ) = ((125000 / 165391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (390273093 / 1000000000) ≤ -Real.log (84609 / 125000) ∧
    -Real.log (84609 / 125000) ≤ (195136547 / 500000000) := by
  have h := checkLog_sound (w := (40391 / 209609)) (n := 12)
    (lo := (390273093 / 1000000000)) (hi := (195136547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 84609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 84609) = 1/(84609 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-195136547 / 500000000) (-390273093 / 1000000000) (Real.log (84609 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (211035341 / 1000000000) ≤ -Real.log (250000 / 308739) ∧
    -Real.log (250000 / 308739) ≤ (105517671 / 500000000) := by
  have h := checkLog_sound (w := (58739 / 558739)) (n := 12)
    (lo := (211035341 / 1000000000)) (hi := (105517671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308739 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(308739 / 250000) = 1/(250000 / 308739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (211035341 / 1000000000) (105517671 / 500000000) (Real.log (308739 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (308739 / 250000) = -Real.log (250000 / 308739) := by
    rw [show ((308739 / 250000) : ℝ) = ((250000 / 308739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (26782193 / 100000000) ≤ -Real.log (191261 / 250000) ∧
    -Real.log (191261 / 250000) ≤ (267821931 / 1000000000) := by
  have h := checkLog_sound (w := (58739 / 441261)) (n := 12)
    (lo := (26782193 / 100000000)) (hi := (267821931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 191261) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 191261) = 1/(191261 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-267821931 / 1000000000) (-26782193 / 100000000) (Real.log (191261 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (105651261 / 500000000) ≤ -Real.log (500000 / 617643) ∧
    -Real.log (500000 / 617643) ≤ (211302523 / 1000000000) := by
  have h := checkLog_sound (w := (117643 / 1117643)) (n := 12)
    (lo := (105651261 / 500000000)) (hi := (211302523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((617643 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(617643 / 500000) = 1/(500000 / 617643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (105651261 / 500000000) (211302523 / 1000000000) (Real.log (617643 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (617643 / 500000) = -Real.log (500000 / 617643) := by
    rw [show ((617643 / 500000) : ℝ) = ((500000 / 617643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (268253371 / 1000000000) ≤ -Real.log (382357 / 500000) ∧
    -Real.log (382357 / 500000) ≤ (67063343 / 250000000) := by
  have h := checkLog_sound (w := (117643 / 882357)) (n := 12)
    (lo := (268253371 / 1000000000)) (hi := (67063343 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 382357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 382357) = 1/(382357 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-67063343 / 250000000) (-268253371 / 1000000000) (Real.log (382357 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (334658037 / 500000000) ≤ -Real.log (500000000000 / 976450612727) ∧
    -Real.log (500000000000 / 976450612727) ≤ (26772643 / 40000000) := by
  have h := checkLog_sound (w := (476450612727 / 1476450612727)) (n := 12)
    (lo := (334658037 / 500000000)) (hi := (26772643 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976450612727 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976450612727 / 500000000000) = 1/(500000000000 / 976450612727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (334658037 / 500000000) (26772643 / 40000000) (Real.log (976450612727 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (976450612727 / 500000000000) = -Real.log (500000000000 / 976450612727) := by
    rw [show ((976450612727 / 500000000000) : ℝ) = ((500000000000 / 976450612727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (670271723 / 1000000000) ≤ -Real.log (500000000000 / 977384202627) ∧
    -Real.log (500000000000 / 977384202627) ≤ (167567931 / 250000000) := by
  have h := checkLog_sound (w := (477384202627 / 1477384202627)) (n := 12)
    (lo := (670271723 / 1000000000)) (hi := (167567931 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((977384202627 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(977384202627 / 500000000000) = 1/(500000000000 / 977384202627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (670271723 / 1000000000) (167567931 / 250000000) (Real.log (977384202627 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (977384202627 / 500000000000) = -Real.log (500000000000 / 977384202627) := by
    rw [show ((977384202627 / 500000000000) : ℝ) = ((500000000000 / 977384202627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (59857159 / 125000000) ≤ -Real.log (500000000000 / 807114362049) ∧
    -Real.log (500000000000 / 807114362049) ≤ (478857273 / 1000000000) := by
  have h := checkLog_sound (w := (307114362049 / 1307114362049)) (n := 12)
    (lo := (59857159 / 125000000)) (hi := (478857273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((807114362049 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(807114362049 / 500000000000) = 1/(500000000000 / 807114362049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (59857159 / 125000000) (478857273 / 1000000000) (Real.log (807114362049 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (807114362049 / 500000000000) = -Real.log (500000000000 / 807114362049) := by
    rw [show ((807114362049 / 500000000000) : ℝ) = ((500000000000 / 807114362049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (479555893 / 1000000000) ≤ -Real.log (500000000000 / 807678426183) ∧
    -Real.log (500000000000 / 807678426183) ≤ (239777947 / 500000000) := by
  have h := checkLog_sound (w := (307678426183 / 1307678426183)) (n := 12)
    (lo := (479555893 / 1000000000)) (hi := (239777947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((807678426183 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(807678426183 / 500000000000) = 1/(500000000000 / 807678426183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (479555893 / 1000000000) (239777947 / 500000000) (Real.log (807678426183 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (807678426183 / 500000000000) = -Real.log (500000000000 / 807678426183) := by
    rw [show ((807678426183 / 500000000000) : ℝ) = ((500000000000 / 807678426183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0384
