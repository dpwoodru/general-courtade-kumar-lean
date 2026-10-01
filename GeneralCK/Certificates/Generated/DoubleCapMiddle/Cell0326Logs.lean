import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0326
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

theorem reflection_log_1_neg : (217816889 / 1000000000) ≤ -Real.log (2560 / 3183) ∧
    -Real.log (2560 / 3183) ≤ (21781689 / 100000000) := by
  have h := checkLog_sound (w := (623 / 5743)) (n := 12)
    (lo := (217816889 / 1000000000)) (hi := (21781689 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3183 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3183 / 2560) = 1/(2560 / 3183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (217816889 / 1000000000) (21781689 / 100000000) (Real.log (3183 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3183 / 2560) = -Real.log (2560 / 3183) := by
    rw [show ((3183 / 2560) : ℝ) = ((2560 / 3183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (139433437 / 500000000) ≤ -Real.log (1937 / 2560) ∧
    -Real.log (1937 / 2560) ≤ (446187 / 1600000) := by
  have h := checkLog_sound (w := (623 / 4497)) (n := 12)
    (lo := (139433437 / 500000000)) (hi := (446187 / 1600000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1937) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1937) = 1/(1937 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-446187 / 1600000) (-139433437 / 500000000) (Real.log (1937 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (43516247 / 200000000) ≤ -Real.log (10240 / 12729) ∧
    -Real.log (10240 / 12729) ≤ (54395309 / 250000000) := by
  have h := checkLog_sound (w := (2489 / 22969)) (n := 12)
    (lo := (43516247 / 200000000)) (hi := (54395309 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12729 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12729 / 10240) = 1/(10240 / 12729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (43516247 / 200000000) (54395309 / 250000000) (Real.log (12729 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12729 / 10240) = -Real.log (10240 / 12729) := by
    rw [show ((12729 / 10240) : ℝ) = ((10240 / 12729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (34809969 / 125000000) ≤ -Real.log (7751 / 10240) ∧
    -Real.log (7751 / 10240) ≤ (278479753 / 1000000000) := by
  have h := checkLog_sound (w := (2489 / 17991)) (n := 12)
    (lo := (34809969 / 125000000)) (hi := (278479753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7751) = 1/(7751 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-278479753 / 1000000000) (-34809969 / 125000000) (Real.log (7751 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (39657151 / 100000000) ≤ -Real.log (1280 / 1903) ∧
    -Real.log (1280 / 1903) ≤ (396571511 / 1000000000) := by
  have h := checkLog_sound (w := (623 / 3183)) (n := 12)
    (lo := (39657151 / 100000000)) (hi := (396571511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1903 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1903 / 1280) = 1/(1280 / 1903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (39657151 / 100000000) (396571511 / 1000000000) (Real.log (1903 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1903 / 1280) = -Real.log (1280 / 1903) := by
    rw [show ((1903 / 1280) : ℝ) = ((1280 / 1903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (333465669 / 500000000) ≤ -Real.log (657 / 1280) ∧
    -Real.log (657 / 1280) ≤ (666931339 / 1000000000) := by
  have h := checkLog_sound (w := (623 / 1937)) (n := 12)
    (lo := (333465669 / 500000000)) (hi := (666931339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 657) = 1/(657 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-666931339 / 1000000000) (-333465669 / 500000000) (Real.log (657 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (198088659 / 500000000) ≤ -Real.log (5120 / 7609) ∧
    -Real.log (5120 / 7609) ≤ (396177319 / 1000000000) := by
  have h := checkLog_sound (w := (2489 / 12729)) (n := 12)
    (lo := (198088659 / 500000000)) (hi := (396177319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7609 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7609 / 5120) = 1/(5120 / 7609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (198088659 / 500000000) (396177319 / 1000000000) (Real.log (7609 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7609 / 5120) = -Real.log (5120 / 7609) := by
    rw [show ((7609 / 5120) : ℝ) = ((5120 / 7609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (166447609 / 250000000) ≤ -Real.log (2631 / 5120) ∧
    -Real.log (2631 / 5120) ≤ (665790437 / 1000000000) := by
  have h := checkLog_sound (w := (2489 / 7751)) (n := 12)
    (lo := (166447609 / 250000000)) (hi := (665790437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2631) = 1/(2631 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-665790437 / 1000000000) (-166447609 / 250000000) (Real.log (2631 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (298260671 / 1000000000) ≤ -Real.log (1000000 / 1347513) ∧
    -Real.log (1000000 / 1347513) ≤ (4660323 / 15625000) := by
  have h := checkLog_sound (w := (347513 / 2347513)) (n := 12)
    (lo := (298260671 / 1000000000)) (hi := (4660323 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1347513 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1347513 / 1000000) = 1/(1000000 / 1347513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (298260671 / 1000000000) (4660323 / 15625000) (Real.log (1347513 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1347513 / 1000000) = -Real.log (1000000 / 1347513) := by
    rw [show ((1347513 / 1000000) : ℝ) = ((1000000 / 1347513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (426964063 / 1000000000) ≤ -Real.log (652487 / 1000000) ∧
    -Real.log (652487 / 1000000) ≤ (13342627 / 31250000) := by
  have h := checkLog_sound (w := (347513 / 1652487)) (n := 12)
    (lo := (426964063 / 1000000000)) (hi := (13342627 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 652487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 652487) = 1/(652487 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-13342627 / 31250000) (-426964063 / 1000000000) (Real.log (652487 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (149289863 / 500000000) ≤ -Real.log (1000000 / 1347943) ∧
    -Real.log (1000000 / 1347943) ≤ (298579727 / 1000000000) := by
  have h := checkLog_sound (w := (347943 / 2347943)) (n := 12)
    (lo := (149289863 / 500000000)) (hi := (298579727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1347943 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1347943 / 1000000) = 1/(1000000 / 1347943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (149289863 / 500000000) (298579727 / 1000000000) (Real.log (1347943 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1347943 / 1000000) = -Real.log (1000000 / 1347943) := by
    rw [show ((1347943 / 1000000) : ℝ) = ((1000000 / 1347943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (427623297 / 1000000000) ≤ -Real.log (652057 / 1000000) ∧
    -Real.log (652057 / 1000000) ≤ (213811649 / 500000000) := by
  have h := checkLog_sound (w := (347943 / 1652057)) (n := 12)
    (lo := (427623297 / 1000000000)) (hi := (213811649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 652057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 652057) = 1/(652057 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-213811649 / 500000000) (-427623297 / 1000000000) (Real.log (652057 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (113258527 / 500000000) ≤ -Real.log (62500 / 78389) ∧
    -Real.log (62500 / 78389) ≤ (45303411 / 200000000) := by
  have h := checkLog_sound (w := (15889 / 140889)) (n := 12)
    (lo := (113258527 / 500000000)) (hi := (45303411 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78389 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78389 / 62500) = 1/(62500 / 78389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (113258527 / 500000000) (45303411 / 200000000) (Real.log (78389 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (78389 / 62500) = -Real.log (62500 / 78389) := by
    rw [show ((78389 / 62500) : ℝ) = ((62500 / 78389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (293329991 / 1000000000) ≤ -Real.log (46611 / 62500) ∧
    -Real.log (46611 / 62500) ≤ (36666249 / 125000000) := by
  have h := checkLog_sound (w := (15889 / 109111)) (n := 12)
    (lo := (293329991 / 1000000000)) (hi := (36666249 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 46611) = 1/(46611 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-36666249 / 125000000) (-293329991 / 1000000000) (Real.log (46611 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (22678571 / 100000000) ≤ -Real.log (1000000 / 1254561) ∧
    -Real.log (1000000 / 1254561) ≤ (226785711 / 1000000000) := by
  have h := checkLog_sound (w := (254561 / 2254561)) (n := 12)
    (lo := (22678571 / 100000000)) (hi := (226785711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1254561 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1254561 / 1000000) = 1/(1000000 / 1254561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (22678571 / 100000000) (226785711 / 1000000000) (Real.log (1254561 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1254561 / 1000000) = -Real.log (1000000 / 1254561) := by
    rw [show ((1254561 / 1000000) : ℝ) = ((1000000 / 1254561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (73445493 / 250000000) ≤ -Real.log (745439 / 1000000) ∧
    -Real.log (745439 / 1000000) ≤ (293781973 / 1000000000) := by
  have h := checkLog_sound (w := (254561 / 1745439)) (n := 12)
    (lo := (73445493 / 250000000)) (hi := (293781973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 745439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 745439) = 1/(745439 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-293781973 / 1000000000) (-73445493 / 250000000) (Real.log (745439 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (362612367 / 500000000) ≤ -Real.log (500000000000 / 1032597584319) ∧
    -Real.log (500000000000 / 1032597584319) ≤ (22663273 / 31250000) := by
  have h := checkLog_sound (w := (32597584319 / 2032597584319)) (n := 12)
    (lo := (16038777 / 500000000)) (hi := (6415511 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1032597584319 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1032597584319 / 1000000000000) = 1/(500000000000 / 1032597584319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (362612367 / 500000000) (22663273 / 31250000) (Real.log (1032597584319 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1032597584319 / 500000000000) = -Real.log (500000000000 / 1032597584319) := by
    rw [show ((1032597584319 / 500000000000) : ℝ) = ((500000000000 / 1032597584319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (726203023 / 1000000000) ≤ -Real.log (250000000000 / 516804129087) ∧
    -Real.log (250000000000 / 516804129087) ≤ (29048121 / 40000000) := by
  have h := checkLog_sound (w := (16804129087 / 1016804129087)) (n := 12)
    (lo := (33055843 / 1000000000)) (hi := (8263961 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((516804129087 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(516804129087 / 500000000000) = 1/(250000000000 / 516804129087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (726203023 / 1000000000) (29048121 / 40000000) (Real.log (516804129087 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (516804129087 / 250000000000) = -Real.log (250000000000 / 516804129087) := by
    rw [show ((516804129087 / 250000000000) : ℝ) = ((250000000000 / 516804129087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (259923523 / 500000000) ≤ -Real.log (125000000000 / 210221299693) ∧
    -Real.log (125000000000 / 210221299693) ≤ (519847047 / 1000000000) := by
  have h := checkLog_sound (w := (85221299693 / 335221299693)) (n := 12)
    (lo := (259923523 / 500000000)) (hi := (519847047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((210221299693 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(210221299693 / 125000000000) = 1/(125000000000 / 210221299693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (259923523 / 500000000) (519847047 / 1000000000) (Real.log (210221299693 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (210221299693 / 125000000000) = -Real.log (125000000000 / 210221299693) := by
    rw [show ((210221299693 / 125000000000) : ℝ) = ((125000000000 / 210221299693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (260283841 / 500000000) ≤ -Real.log (250000000000 / 420745694819) ∧
    -Real.log (250000000000 / 420745694819) ≤ (520567683 / 1000000000) := by
  have h := checkLog_sound (w := (170745694819 / 670745694819)) (n := 12)
    (lo := (260283841 / 500000000)) (hi := (520567683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((420745694819 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(420745694819 / 250000000000) = 1/(250000000000 / 420745694819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (260283841 / 500000000) (520567683 / 1000000000) (Real.log (420745694819 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (420745694819 / 250000000000) = -Real.log (250000000000 / 420745694819) := by
    rw [show ((420745694819 / 250000000000) : ℝ) = ((250000000000 / 420745694819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0326
