import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0218
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

theorem reflection_log_1_neg : (128772489 / 500000000) ≤ -Real.log (160 / 207) ∧
    -Real.log (160 / 207) ≤ (257544979 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 367)) (n := 12)
    (lo := (128772489 / 500000000)) (hi := (257544979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((207 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(207 / 160) = 1/(160 / 207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (128772489 / 500000000) (257544979 / 1000000000) (Real.log (207 / 160)) := by
  have h := reflection_log_1_neg
  have he : Real.log (207 / 160) = -Real.log (160 / 207) := by
    rw [show ((207 / 160) : ℝ) = ((160 / 207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (86946499 / 250000000) ≤ -Real.log (113 / 160) ∧
    -Real.log (113 / 160) ≤ (347785997 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 273)) (n := 12)
    (lo := (86946499 / 250000000)) (hi := (347785997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 113) = 1/(113 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-347785997 / 1000000000) (-86946499 / 250000000) (Real.log (113 / 160)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (32136497 / 125000000) ≤ -Real.log (5120 / 6621) ∧
    -Real.log (5120 / 6621) ≤ (257091977 / 1000000000) := by
  have h := checkLog_sound (w := (1501 / 11741)) (n := 12)
    (lo := (32136497 / 125000000)) (hi := (257091977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6621 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6621 / 5120) = 1/(5120 / 6621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (32136497 / 125000000) (257091977 / 1000000000) (Real.log (6621 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6621 / 5120) = -Real.log (5120 / 6621) := by
    rw [show ((6621 / 5120) : ℝ) = ((5120 / 6621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (173478347 / 500000000) ≤ -Real.log (3619 / 5120) ∧
    -Real.log (3619 / 5120) ≤ (69391339 / 200000000) := by
  have h := checkLog_sound (w := (1501 / 8739)) (n := 12)
    (lo := (173478347 / 500000000)) (hi := (69391339 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3619) = 1/(3619 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-69391339 / 200000000) (-173478347 / 500000000) (Real.log (3619 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (462160451 / 1000000000) ≤ -Real.log (80 / 127) ∧
    -Real.log (80 / 127) ≤ (115540113 / 250000000) := by
  have h := checkLog_sound (w := (47 / 207)) (n := 12)
    (lo := (462160451 / 1000000000)) (hi := (115540113 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(127 / 80) = 1/(80 / 127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (462160451 / 1000000000) (115540113 / 250000000) (Real.log (127 / 80)) := by
  have h := reflection_log_5_neg
  have he : Real.log (127 / 80) = -Real.log (80 / 127) := by
    rw [show ((127 / 80) : ℝ) = ((80 / 127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (27672471 / 31250000) ≤ -Real.log (33 / 80) ∧
    -Real.log (33 / 80) ≤ (442759537 / 500000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 33) = 1/(33 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-442759537 / 500000000) (-27672471 / 31250000) (Real.log (33 / 80)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (46142199 / 100000000) ≤ -Real.log (2560 / 4061) ∧
    -Real.log (2560 / 4061) ≤ (461421991 / 1000000000) := by
  have h := checkLog_sound (w := (1501 / 6621)) (n := 12)
    (lo := (46142199 / 100000000)) (hi := (461421991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4061 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4061 / 2560) = 1/(2560 / 4061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (46142199 / 100000000) (461421991 / 1000000000) (Real.log (4061 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4061 / 2560) = -Real.log (2560 / 4061) := by
    rw [show ((4061 / 2560) : ℝ) = ((2560 / 4061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (882682191 / 1000000000) ≤ -Real.log (1059 / 2560) ∧
    -Real.log (1059 / 2560) ≤ (882682193 / 1000000000) := by
  have h := checkLog_sound (w := (221 / 2339)) (n := 12)
    (lo := (189535011 / 1000000000)) (hi := (47383753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1059) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1059) = 1/(1059 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-882682193 / 1000000000) (-882682191 / 1000000000) (Real.log (1059 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (175885871 / 500000000) ≤ -Real.log (62500 / 88849) ∧
    -Real.log (62500 / 88849) ≤ (351771743 / 1000000000) := by
  have h := checkLog_sound (w := (26349 / 151349)) (n := 12)
    (lo := (175885871 / 500000000)) (hi := (351771743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((88849 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(88849 / 62500) = 1/(62500 / 88849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (175885871 / 500000000) (351771743 / 1000000000) (Real.log (88849 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (88849 / 62500) = -Real.log (62500 / 88849) := by
    rw [show ((88849 / 62500) : ℝ) = ((62500 / 88849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (273730973 / 500000000) ≤ -Real.log (36151 / 62500) ∧
    -Real.log (36151 / 62500) ≤ (547461947 / 1000000000) := by
  have h := checkLog_sound (w := (26349 / 98651)) (n := 12)
    (lo := (273730973 / 500000000)) (hi := (547461947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 36151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 36151) = 1/(36151 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-547461947 / 1000000000) (-273730973 / 500000000) (Real.log (36151 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (35238847 / 100000000) ≤ -Real.log (1000000 / 1422461) ∧
    -Real.log (1000000 / 1422461) ≤ (352388471 / 1000000000) := by
  have h := checkLog_sound (w := (422461 / 2422461)) (n := 12)
    (lo := (35238847 / 100000000)) (hi := (352388471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1422461 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1422461 / 1000000) = 1/(1000000 / 1422461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (35238847 / 100000000) (352388471 / 1000000000) (Real.log (1422461 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1422461 / 1000000) = -Real.log (1000000 / 1422461) := by
    rw [show ((1422461 / 1000000) : ℝ) = ((1000000 / 1422461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (274489653 / 500000000) ≤ -Real.log (577539 / 1000000) ∧
    -Real.log (577539 / 1000000) ≤ (548979307 / 1000000000) := by
  have h := checkLog_sound (w := (422461 / 1577539)) (n := 12)
    (lo := (274489653 / 500000000)) (hi := (548979307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 577539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 577539) = 1/(577539 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-548979307 / 1000000000) (-274489653 / 500000000) (Real.log (577539 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (68174213 / 250000000) ≤ -Real.log (500000 / 656751) ∧
    -Real.log (500000 / 656751) ≤ (272696853 / 1000000000) := by
  have h := checkLog_sound (w := (156751 / 1156751)) (n := 12)
    (lo := (68174213 / 250000000)) (hi := (272696853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((656751 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(656751 / 500000) = 1/(500000 / 656751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (68174213 / 250000000) (272696853 / 1000000000) (Real.log (656751 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (656751 / 500000) = -Real.log (500000 / 656751) := by
    rw [show ((656751 / 500000) : ℝ) = ((500000 / 656751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (376151967 / 1000000000) ≤ -Real.log (343249 / 500000) ∧
    -Real.log (343249 / 500000) ≤ (11754749 / 31250000) := by
  have h := checkLog_sound (w := (156751 / 843249)) (n := 12)
    (lo := (376151967 / 1000000000)) (hi := (11754749 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 343249) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 343249) = 1/(343249 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-11754749 / 31250000) (-376151967 / 1000000000) (Real.log (343249 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (54648971 / 200000000) ≤ -Real.log (500000 / 657111) ∧
    -Real.log (500000 / 657111) ≤ (34155607 / 125000000) := by
  have h := checkLog_sound (w := (157111 / 1157111)) (n := 12)
    (lo := (54648971 / 200000000)) (hi := (34155607 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657111 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657111 / 500000) = 1/(500000 / 657111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (54648971 / 200000000) (34155607 / 125000000) (Real.log (657111 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (657111 / 500000) = -Real.log (500000 / 657111) := by
    rw [show ((657111 / 500000) : ℝ) = ((500000 / 657111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (188600659 / 500000000) ≤ -Real.log (342889 / 500000) ∧
    -Real.log (342889 / 500000) ≤ (377201319 / 1000000000) := by
  have h := checkLog_sound (w := (157111 / 842889)) (n := 12)
    (lo := (188600659 / 500000000)) (hi := (377201319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 342889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 342889) = 1/(342889 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-377201319 / 1000000000) (-188600659 / 500000000) (Real.log (342889 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (112404211 / 125000000) ≤ -Real.log (500000000000 / 1228859505961) ∧
    -Real.log (500000000000 / 1228859505961) ≤ (89923369 / 100000000) := by
  have h := checkLog_sound (w := (228859505961 / 2228859505961)) (n := 12)
    (lo := (51521627 / 250000000)) (hi := (206086509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1228859505961 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1228859505961 / 1000000000000) = 1/(500000000000 / 1228859505961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (112404211 / 125000000) (89923369 / 100000000) (Real.log (1228859505961 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1228859505961 / 500000000000) = -Real.log (500000000000 / 1228859505961) := by
    rw [show ((1228859505961 / 500000000000) : ℝ) = ((500000000000 / 1228859505961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (36054711 / 40000000) ≤ -Real.log (500000000000 / 1231484800161) ∧
    -Real.log (500000000000 / 1231484800161) ≤ (901367777 / 1000000000) := by
  have h := checkLog_sound (w := (231484800161 / 2231484800161)) (n := 12)
    (lo := (41644119 / 200000000)) (hi := (52055149 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1231484800161 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1231484800161 / 1000000000000) = 1/(500000000000 / 1231484800161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (36054711 / 40000000) (901367777 / 1000000000) (Real.log (1231484800161 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1231484800161 / 500000000000) = -Real.log (500000000000 / 1231484800161) := by
    rw [show ((1231484800161 / 500000000000) : ℝ) = ((500000000000 / 1231484800161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (648848819 / 1000000000) ≤ -Real.log (250000000000 / 478334241323) ∧
    -Real.log (250000000000 / 478334241323) ≤ (32442441 / 50000000) := by
  have h := checkLog_sound (w := (228334241323 / 728334241323)) (n := 12)
    (lo := (648848819 / 1000000000)) (hi := (32442441 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((478334241323 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(478334241323 / 250000000000) = 1/(250000000000 / 478334241323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (648848819 / 1000000000) (32442441 / 50000000) (Real.log (478334241323 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (478334241323 / 250000000000) = -Real.log (250000000000 / 478334241323) := by
    rw [show ((478334241323 / 250000000000) : ℝ) = ((250000000000 / 478334241323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (325223087 / 500000000) ≤ -Real.log (500000000000 / 958197842451) ∧
    -Real.log (500000000000 / 958197842451) ≤ (26017847 / 40000000) := by
  have h := checkLog_sound (w := (458197842451 / 1458197842451)) (n := 12)
    (lo := (325223087 / 500000000)) (hi := (26017847 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((958197842451 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(958197842451 / 500000000000) = 1/(500000000000 / 958197842451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (325223087 / 500000000) (26017847 / 40000000) (Real.log (958197842451 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (958197842451 / 500000000000) = -Real.log (500000000000 / 958197842451) := by
    rw [show ((958197842451 / 500000000000) : ℝ) = ((500000000000 / 958197842451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0218
