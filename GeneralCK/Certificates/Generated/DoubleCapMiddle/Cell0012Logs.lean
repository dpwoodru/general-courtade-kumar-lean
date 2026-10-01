import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0012
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

theorem reflection_log_1_neg : (12646361 / 31250000) ≤ -Real.log (2560 / 3837) ∧
    -Real.log (2560 / 3837) ≤ (404683553 / 1000000000) := by
  have h := checkLog_sound (w := (1277 / 6397)) (n := 12)
    (lo := (12646361 / 31250000)) (hi := (404683553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3837 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3837 / 2560) = 1/(2560 / 3837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (12646361 / 31250000) (404683553 / 1000000000) (Real.log (3837 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3837 / 2560) = -Real.log (2560 / 3837) := by
    rw [show ((3837 / 2560) : ℝ) = ((2560 / 3837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (172701543 / 250000000) ≤ -Real.log (1283 / 2560) ∧
    -Real.log (1283 / 2560) ≤ (690806173 / 1000000000) := by
  have h := checkLog_sound (w := (1277 / 3843)) (n := 12)
    (lo := (172701543 / 250000000)) (hi := (690806173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1283) = 1/(1283 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-690806173 / 1000000000) (-172701543 / 250000000) (Real.log (1283 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (201950693 / 500000000) ≤ -Real.log (1280 / 1917) ∧
    -Real.log (1280 / 1917) ≤ (403901387 / 1000000000) := by
  have h := checkLog_sound (w := (637 / 3197)) (n := 12)
    (lo := (201950693 / 500000000)) (hi := (403901387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1917 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1917 / 1280) = 1/(1280 / 1917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (201950693 / 500000000) (403901387 / 1000000000) (Real.log (1917 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1917 / 1280) = -Real.log (1280 / 1917) := by
    rw [show ((1917 / 1280) : ℝ) = ((1280 / 1917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (86058829 / 125000000) ≤ -Real.log (643 / 1280) ∧
    -Real.log (643 / 1280) ≤ (688470633 / 1000000000) := by
  have h := checkLog_sound (w := (637 / 1923)) (n := 12)
    (lo := (86058829 / 125000000)) (hi := (688470633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 643) = 1/(643 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-688470633 / 1000000000) (-86058829 / 125000000) (Real.log (643 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (345987309 / 500000000) ≤ -Real.log (1280 / 2557) ∧
    -Real.log (1280 / 2557) ≤ (691974619 / 1000000000) := by
  have h := checkLog_sound (w := (1277 / 3837)) (n := 12)
    (lo := (345987309 / 500000000)) (hi := (691974619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2557 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2557 / 1280) = 1/(1280 / 2557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (345987309 / 500000000) (691974619 / 1000000000) (Real.log (2557 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2557 / 1280) = -Real.log (1280 / 2557) := by
    rw [show ((2557 / 1280) : ℝ) = ((1280 / 2557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (6056003063 / 1000000000) ≤ -Real.log (3 / 1280) ∧
    -Real.log (3 / 1280) ≤ (11828131 / 1953125) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(5 / 3) = 1/(3 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-11828131 / 1953125) (-6056003063 / 1000000000) (Real.log (3 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (690800679 / 1000000000) ≤ -Real.log (640 / 1277) ∧
    -Real.log (640 / 1277) ≤ (17270017 / 25000000) := by
  have h := checkLog_sound (w := (637 / 1917)) (n := 12)
    (lo := (690800679 / 1000000000)) (hi := (17270017 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1277 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1277 / 640) = 1/(640 / 1277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (690800679 / 1000000000) (17270017 / 25000000) (Real.log (1277 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1277 / 640) = -Real.log (640 / 1277) := by
    rw [show ((1277 / 640) : ℝ) = ((640 / 1277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (5362855883 / 1000000000) ≤ -Real.log (3 / 640) ∧
    -Real.log (3 / 640) ≤ (5362855891 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(5 / 3) = 1/(3 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-5362855891 / 1000000000) (-5362855883 / 1000000000) (Real.log (3 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (114416917 / 200000000) ≤ -Real.log (1000000 / 1771957) ∧
    -Real.log (1000000 / 1771957) ≤ (286042293 / 500000000) := by
  have h := checkLog_sound (w := (771957 / 2771957)) (n := 12)
    (lo := (114416917 / 200000000)) (hi := (286042293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1771957 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1771957 / 1000000) = 1/(1000000 / 1771957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (114416917 / 200000000) (286042293 / 500000000) (Real.log (1771957 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1771957 / 1000000) = -Real.log (1000000 / 1771957) := by
    rw [show ((1771957 / 1000000) : ℝ) = ((1000000 / 1771957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (147822107 / 100000000) ≤ -Real.log (228043 / 1000000) ∧
    -Real.log (228043 / 1000000) ≤ (1478221073 / 1000000000) := by
  have h := checkLog_sound (w := (21957 / 478043)) (n := 12)
    (lo := (9192671 / 100000000)) (hi := (91926711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228043) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 228043) = 1/(228043 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1478221073 / 1000000000) (-147822107 / 100000000) (Real.log (228043 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (574126003 / 1000000000) ≤ -Real.log (500000 / 887789) ∧
    -Real.log (500000 / 887789) ≤ (143531501 / 250000000) := by
  have h := checkLog_sound (w := (387789 / 1387789)) (n := 12)
    (lo := (574126003 / 1000000000)) (hi := (143531501 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((887789 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(887789 / 500000) = 1/(500000 / 887789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (574126003 / 1000000000) (143531501 / 250000000) (Real.log (887789 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (887789 / 500000) = -Real.log (500000 / 887789) := by
    rw [show ((887789 / 500000) : ℝ) = ((500000 / 887789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1494227069 / 1000000000) ≤ -Real.log (112211 / 500000) ∧
    -Real.log (112211 / 500000) ≤ (11673649 / 7812500) := by
  have h := checkLog_sound (w := (12789 / 237211)) (n := 12)
    (lo := (107932709 / 1000000000)) (hi := (10793271 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112211) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 112211) = 1/(112211 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-11673649 / 7812500) (-1494227069 / 1000000000) (Real.log (112211 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (250440671 / 500000000) ≤ -Real.log (40000 / 66007) ∧
    -Real.log (40000 / 66007) ≤ (500881343 / 1000000000) := by
  have h := checkLog_sound (w := (26007 / 106007)) (n := 12)
    (lo := (250440671 / 500000000)) (hi := (500881343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66007 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(66007 / 40000) = 1/(40000 / 66007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (250440671 / 500000000) (500881343 / 1000000000) (Real.log (66007 / 40000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (66007 / 40000) = -Real.log (40000 / 66007) := by
    rw [show ((66007 / 40000) : ℝ) = ((40000 / 66007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (131290281 / 125000000) ≤ -Real.log (13993 / 40000) ∧
    -Real.log (13993 / 40000) ≤ (4201289 / 4000000) := by
  have h := checkLog_sound (w := (6007 / 33993)) (n := 12)
    (lo := (89293767 / 250000000)) (hi := (357175069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 13993) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 13993) = 1/(13993 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-4201289 / 4000000) (-131290281 / 125000000) (Real.log (13993 / 40000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (125827261 / 250000000) ≤ -Real.log (500000 / 827093) ∧
    -Real.log (500000 / 827093) ≤ (100661809 / 200000000) := by
  have h := checkLog_sound (w := (327093 / 1327093)) (n := 12)
    (lo := (125827261 / 250000000)) (hi := (100661809 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((827093 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(827093 / 500000) = 1/(500000 / 827093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (125827261 / 250000000) (100661809 / 200000000) (Real.log (827093 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (827093 / 500000) = -Real.log (500000 / 827093) := by
    rw [show ((827093 / 500000) : ℝ) = ((500000 / 827093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (53092711 / 50000000) ≤ -Real.log (172907 / 500000) ∧
    -Real.log (172907 / 500000) ≤ (530927111 / 500000000) := by
  have h := checkLog_sound (w := (77093 / 422907)) (n := 12)
    (lo := (2304419 / 6250000)) (hi := (368707041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 172907) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 172907) = 1/(172907 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-530927111 / 500000000) (-53092711 / 50000000) (Real.log (172907 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (410061131 / 200000000) ≤ -Real.log (25000000000 / 194256894533) ∧
    -Real.log (25000000000 / 194256894533) ≤ (1025152829 / 500000000) := by
  have h := checkLog_sound (w := (94256894533 / 294256894533)) (n := 12)
    (lo := (132802259 / 200000000)) (hi := (20750353 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((194256894533 / 100000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(194256894533 / 100000000000) = 1/(25000000000 / 194256894533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (410061131 / 200000000) (1025152829 / 500000000) (Real.log (194256894533 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (194256894533 / 25000000000) = -Real.log (25000000000 / 194256894533) := by
    rw [show ((194256894533 / 25000000000) : ℝ) = ((25000000000 / 194256894533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2068353073 / 1000000000) ≤ -Real.log (125000000000 / 988972783417) ∧
    -Real.log (125000000000 / 988972783417) ≤ (517088269 / 250000000) := by
  have h := checkLog_sound (w := (488972783417 / 1488972783417)) (n := 12)
    (lo := (682058713 / 1000000000)) (hi := (341029357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((988972783417 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(988972783417 / 500000000000) = 1/(125000000000 / 988972783417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2068353073 / 1000000000) (517088269 / 250000000) (Real.log (988972783417 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (988972783417 / 125000000000) = -Real.log (125000000000 / 988972783417) := by
    rw [show ((988972783417 / 125000000000) : ℝ) = ((125000000000 / 988972783417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1551203591 / 1000000000) ≤ -Real.log (250000000000 / 1179286071607) ∧
    -Real.log (250000000000 / 1179286071607) ≤ (775601797 / 500000000) := by
  have h := checkLog_sound (w := (179286071607 / 2179286071607)) (n := 12)
    (lo := (164909231 / 1000000000)) (hi := (10306827 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1179286071607 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1179286071607 / 1000000000000) = 1/(250000000000 / 1179286071607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1551203591 / 1000000000) (775601797 / 500000000) (Real.log (1179286071607 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1179286071607 / 250000000000) = -Real.log (250000000000 / 1179286071607) := by
    rw [show ((1179286071607 / 250000000000) : ℝ) = ((250000000000 / 1179286071607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (6113919 / 3906250) ≤ -Real.log (15625000000 / 74741497597) ∧
    -Real.log (15625000000 / 74741497597) ≤ (1565163267 / 1000000000) := by
  have h := checkLog_sound (w := (12241497597 / 137241497597)) (n := 12)
    (lo := (22358613 / 125000000)) (hi := (35773781 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74741497597 / 62500000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(74741497597 / 62500000000) = 1/(15625000000 / 74741497597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (6113919 / 3906250) (1565163267 / 1000000000) (Real.log (74741497597 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (74741497597 / 15625000000) = -Real.log (15625000000 / 74741497597) := by
    rw [show ((74741497597 / 15625000000) : ℝ) = ((15625000000 / 74741497597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0012
