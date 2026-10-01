import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0306
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

theorem reflection_log_1_neg : (44503671 / 200000000) ≤ -Real.log (1280 / 1599) ∧
    -Real.log (1280 / 1599) ≤ (55629589 / 250000000) := by
  have h := checkLog_sound (w := (319 / 2879)) (n := 12)
    (lo := (44503671 / 200000000)) (hi := (55629589 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1599 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1599 / 1280) = 1/(1280 / 1599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (44503671 / 200000000) (55629589 / 250000000) (Real.log (1599 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1599 / 1280) = -Real.log (1280 / 1599) := by
    rw [show ((1599 / 1280) : ℝ) = ((1280 / 1599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (286640947 / 1000000000) ≤ -Real.log (961 / 1280) ∧
    -Real.log (961 / 1280) ≤ (71660237 / 250000000) := by
  have h := checkLog_sound (w := (319 / 2241)) (n := 12)
    (lo := (286640947 / 1000000000)) (hi := (71660237 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 961) = 1/(961 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-71660237 / 250000000) (-286640947 / 1000000000) (Real.log (961 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (111141903 / 500000000) ≤ -Real.log (10240 / 12789) ∧
    -Real.log (10240 / 12789) ≤ (222283807 / 1000000000) := by
  have h := checkLog_sound (w := (2549 / 23029)) (n := 12)
    (lo := (111141903 / 500000000)) (hi := (222283807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12789 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12789 / 10240) = 1/(10240 / 12789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (111141903 / 500000000) (222283807 / 1000000000) (Real.log (12789 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12789 / 10240) = -Real.log (10240 / 12789) := by
    rw [show ((12789 / 10240) : ℝ) = ((10240 / 12789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (57250161 / 200000000) ≤ -Real.log (7691 / 10240) ∧
    -Real.log (7691 / 10240) ≤ (143125403 / 500000000) := by
  have h := checkLog_sound (w := (2549 / 17931)) (n := 12)
    (lo := (57250161 / 200000000)) (hi := (143125403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7691) = 1/(7691 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-143125403 / 500000000) (-57250161 / 200000000) (Real.log (7691 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (202211449 / 500000000) ≤ -Real.log (640 / 959) ∧
    -Real.log (640 / 959) ≤ (404422899 / 1000000000) := by
  have h := checkLog_sound (w := (319 / 1599)) (n := 12)
    (lo := (202211449 / 500000000)) (hi := (404422899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((959 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(959 / 640) = 1/(640 / 959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (202211449 / 500000000) (404422899 / 1000000000) (Real.log (959 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (959 / 640) = -Real.log (640 / 959) := by
    rw [show ((959 / 640) : ℝ) = ((640 / 959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (690027053 / 1000000000) ≤ -Real.log (321 / 640) ∧
    -Real.log (321 / 640) ≤ (345013527 / 500000000) := by
  have h := checkLog_sound (w := (319 / 961)) (n := 12)
    (lo := (690027053 / 1000000000)) (hi := (345013527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 321) = 1/(321 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-345013527 / 500000000) (-690027053 / 1000000000) (Real.log (321 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (404031789 / 1000000000) ≤ -Real.log (5120 / 7669) ∧
    -Real.log (5120 / 7669) ≤ (40403179 / 100000000) := by
  have h := checkLog_sound (w := (2549 / 12789)) (n := 12)
    (lo := (404031789 / 1000000000)) (hi := (40403179 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7669 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7669 / 5120) = 1/(5120 / 7669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (404031789 / 1000000000) (40403179 / 100000000) (Real.log (7669 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7669 / 5120) = -Real.log (5120 / 7669) := by
    rw [show ((7669 / 5120) : ℝ) = ((5120 / 7669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (68885951 / 100000000) ≤ -Real.log (2571 / 5120) ∧
    -Real.log (2571 / 5120) ≤ (688859511 / 1000000000) := by
  have h := checkLog_sound (w := (2549 / 7691)) (n := 12)
    (lo := (68885951 / 100000000)) (hi := (688859511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2571) = 1/(2571 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-688859511 / 1000000000) (-68885951 / 100000000) (Real.log (2571 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (304614407 / 1000000000) ≤ -Real.log (500000 / 678051) ∧
    -Real.log (500000 / 678051) ≤ (38076801 / 125000000) := by
  have h := checkLog_sound (w := (178051 / 1178051)) (n := 12)
    (lo := (304614407 / 1000000000)) (hi := (38076801 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((678051 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(678051 / 500000) = 1/(500000 / 678051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (304614407 / 1000000000) (38076801 / 125000000) (Real.log (678051 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (678051 / 500000) = -Real.log (500000 / 678051) := by
    rw [show ((678051 / 500000) : ℝ) = ((500000 / 678051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (8804299 / 20000000) ≤ -Real.log (321949 / 500000) ∧
    -Real.log (321949 / 500000) ≤ (440214951 / 1000000000) := by
  have h := checkLog_sound (w := (178051 / 821949)) (n := 12)
    (lo := (8804299 / 20000000)) (hi := (440214951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 321949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 321949) = 1/(321949 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-440214951 / 1000000000) (-8804299 / 20000000) (Real.log (321949 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (15246609 / 50000000) ≤ -Real.log (1000000 / 1356533) ∧
    -Real.log (1000000 / 1356533) ≤ (304932181 / 1000000000) := by
  have h := checkLog_sound (w := (356533 / 2356533)) (n := 12)
    (lo := (15246609 / 50000000)) (hi := (304932181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1356533 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1356533 / 1000000) = 1/(1000000 / 1356533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (15246609 / 50000000) (304932181 / 1000000000) (Real.log (1356533 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1356533 / 1000000) = -Real.log (1000000 / 1356533) := by
    rw [show ((1356533 / 1000000) : ℝ) = ((1000000 / 1356533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (88176907 / 200000000) ≤ -Real.log (643467 / 1000000) ∧
    -Real.log (643467 / 1000000) ≤ (55110567 / 125000000) := by
  have h := checkLog_sound (w := (356533 / 1643467)) (n := 12)
    (lo := (88176907 / 200000000)) (hi := (55110567 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 643467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 643467) = 1/(643467 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-55110567 / 125000000) (-88176907 / 200000000) (Real.log (643467 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (57967739 / 250000000) ≤ -Real.log (1000000 / 1260957) ∧
    -Real.log (1000000 / 1260957) ≤ (231870957 / 1000000000) := by
  have h := checkLog_sound (w := (260957 / 2260957)) (n := 12)
    (lo := (57967739 / 250000000)) (hi := (231870957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1260957 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1260957 / 1000000) = 1/(1000000 / 1260957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (57967739 / 250000000) (231870957 / 1000000000) (Real.log (1260957 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1260957 / 1000000) = -Real.log (1000000 / 1260957) := by
    rw [show ((1260957 / 1000000) : ℝ) = ((1000000 / 1260957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (75599793 / 250000000) ≤ -Real.log (739043 / 1000000) ∧
    -Real.log (739043 / 1000000) ≤ (302399173 / 1000000000) := by
  have h := checkLog_sound (w := (260957 / 1739043)) (n := 12)
    (lo := (75599793 / 250000000)) (hi := (302399173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 739043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 739043) = 1/(739043 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-302399173 / 1000000000) (-75599793 / 250000000) (Real.log (739043 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (232139763 / 1000000000) ≤ -Real.log (62500 / 78831) ∧
    -Real.log (62500 / 78831) ≤ (58034941 / 250000000) := by
  have h := checkLog_sound (w := (16331 / 141331)) (n := 12)
    (lo := (232139763 / 1000000000)) (hi := (58034941 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78831 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78831 / 62500) = 1/(62500 / 78831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (232139763 / 1000000000) (58034941 / 250000000) (Real.log (78831 / 62500)) := by
  have h := reflection_log_15_neg
  have he : Real.log (78831 / 62500) = -Real.log (62500 / 78831) := by
    rw [show ((78831 / 62500) : ℝ) = ((62500 / 78831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (302857979 / 1000000000) ≤ -Real.log (46169 / 62500) ∧
    -Real.log (46169 / 62500) ≤ (15142899 / 50000000) := by
  have h := checkLog_sound (w := (16331 / 108669)) (n := 12)
    (lo := (302857979 / 1000000000)) (hi := (15142899 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 46169) = 1/(46169 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-15142899 / 50000000) (-302857979 / 1000000000) (Real.log (46169 / 62500)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (744829357 / 1000000000) ≤ -Real.log (312500000 / 658150631) ∧
    -Real.log (312500000 / 658150631) ≤ (744829359 / 1000000000) := by
  have h := checkLog_sound (w := (33150631 / 1283150631)) (n := 12)
    (lo := (51682177 / 1000000000)) (hi := (25841089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((658150631 / 625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(658150631 / 625000000) = 1/(312500000 / 658150631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (744829357 / 1000000000) (744829359 / 1000000000) (Real.log (658150631 / 312500000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (658150631 / 312500000) = -Real.log (312500000 / 658150631) := by
    rw [show ((658150631 / 312500000) : ℝ) = ((312500000 / 658150631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (372908357 / 500000000) ≤ -Real.log (125000000000 / 263520312619) ∧
    -Real.log (125000000000 / 263520312619) ≤ (186454179 / 250000000) := by
  have h := checkLog_sound (w := (13520312619 / 513520312619)) (n := 12)
    (lo := (26334767 / 500000000)) (hi := (10533907 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((263520312619 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(263520312619 / 250000000000) = 1/(125000000000 / 263520312619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (372908357 / 500000000) (186454179 / 250000000) (Real.log (263520312619 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (263520312619 / 125000000000) = -Real.log (125000000000 / 263520312619) := by
    rw [show ((263520312619 / 125000000000) : ℝ) = ((125000000000 / 263520312619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (534270129 / 1000000000) ≤ -Real.log (500000000000 / 853101240387) ∧
    -Real.log (500000000000 / 853101240387) ≤ (53427013 / 100000000) := by
  have h := checkLog_sound (w := (353101240387 / 1353101240387)) (n := 12)
    (lo := (534270129 / 1000000000)) (hi := (53427013 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((853101240387 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(853101240387 / 500000000000) = 1/(500000000000 / 853101240387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (534270129 / 1000000000) (53427013 / 100000000) (Real.log (853101240387 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (853101240387 / 500000000000) = -Real.log (500000000000 / 853101240387) := by
    rw [show ((853101240387 / 500000000000) : ℝ) = ((500000000000 / 853101240387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (534997743 / 1000000000) ≤ -Real.log (500000000000 / 853722194547) ∧
    -Real.log (500000000000 / 853722194547) ≤ (33437359 / 62500000) := by
  have h := checkLog_sound (w := (353722194547 / 1353722194547)) (n := 12)
    (lo := (534997743 / 1000000000)) (hi := (33437359 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((853722194547 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(853722194547 / 500000000000) = 1/(500000000000 / 853722194547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (534997743 / 1000000000) (33437359 / 62500000) (Real.log (853722194547 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (853722194547 / 500000000000) = -Real.log (500000000000 / 853722194547) := by
    rw [show ((853722194547 / 500000000000) : ℝ) = ((500000000000 / 853722194547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0306
