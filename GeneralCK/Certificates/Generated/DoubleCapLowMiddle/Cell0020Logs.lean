import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0020
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

theorem reflection_log_1_neg : (85234733 / 125000000) ≤ -Real.log (20480 / 40501) ∧
    -Real.log (20480 / 40501) ≤ (136375573 / 200000000) := by
  have h := checkLog_sound (w := (20021 / 60981)) (n := 12)
    (lo := (85234733 / 125000000)) (hi := (136375573 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40501 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40501 / 20480) = 1/(20480 / 40501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (85234733 / 125000000) (136375573 / 200000000) (Real.log (40501 / 20480)) := by
  have h := reflection_log_1_neg
  have he : Real.log (40501 / 20480) = -Real.log (20480 / 40501) := by
    rw [show ((40501 / 20480) : ℝ) = ((20480 / 40501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1899076933 / 500000000) ≤ -Real.log (459 / 20480) ∧
    -Real.log (459 / 20480) ≤ (237384617 / 62500000) := by
  have h := checkLog_sound (w := (181 / 1099)) (n := 12)
    (lo := (166208983 / 500000000)) (hi := (332417967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 459) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(640 / 459) = 1/(459 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-237384617 / 62500000) (-1899076933 / 500000000) (Real.log (459 / 20480)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (136356807 / 200000000) ≤ -Real.log (51200 / 101243) ∧
    -Real.log (51200 / 101243) ≤ (170446009 / 250000000) := by
  have h := checkLog_sound (w := (50043 / 152443)) (n := 12)
    (lo := (136356807 / 200000000)) (hi := (170446009 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101243 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(101243 / 51200) = 1/(51200 / 101243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (136356807 / 200000000) (170446009 / 250000000) (Real.log (101243 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (101243 / 51200) = -Real.log (51200 / 101243) := by
    rw [show ((101243 / 51200) : ℝ) = ((51200 / 101243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3789909081 / 1000000000) ≤ -Real.log (1157 / 51200) ∧
    -Real.log (1157 / 51200) ≤ (3789909087 / 1000000000) := by
  have h := checkLog_sound (w := (443 / 2757)) (n := 12)
    (lo := (324173181 / 1000000000)) (hi := (162086591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1157) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1600 / 1157) = 1/(1157 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3789909087 / 1000000000) (-3789909081 / 1000000000) (Real.log (1157 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (670480103 / 1000000000) ≤ -Real.log (10240 / 20021) ∧
    -Real.log (10240 / 20021) ≤ (83810013 / 125000000) := by
  have h := checkLog_sound (w := (9781 / 30261)) (n := 12)
    (lo := (670480103 / 1000000000)) (hi := (83810013 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20021 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20021 / 10240) = 1/(10240 / 20021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (670480103 / 1000000000) (83810013 / 125000000) (Real.log (20021 / 10240)) := by
  have h := reflection_log_5_neg
  have he : Real.log (20021 / 10240) = -Real.log (10240 / 20021) := by
    rw [show ((20021 / 10240) : ℝ) = ((10240 / 20021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1552503343 / 500000000) ≤ -Real.log (459 / 10240) ∧
    -Real.log (459 / 10240) ≤ (3105006691 / 1000000000) := by
  have h := checkLog_sound (w := (181 / 1099)) (n := 12)
    (lo := (166208983 / 500000000)) (hi := (332417967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 459) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 459) = 1/(459 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3105006691 / 1000000000) (-1552503343 / 500000000) (Real.log (459 / 10240)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (167572571 / 250000000) ≤ -Real.log (25600 / 50043) ∧
    -Real.log (25600 / 50043) ≤ (134058057 / 200000000) := by
  have h := checkLog_sound (w := (24443 / 75643)) (n := 12)
    (lo := (167572571 / 250000000)) (hi := (134058057 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50043 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50043 / 25600) = 1/(25600 / 50043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (167572571 / 250000000) (134058057 / 200000000) (Real.log (50043 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (50043 / 25600) = -Real.log (25600 / 50043) := by
    rw [show ((50043 / 25600) : ℝ) = ((25600 / 50043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3096761901 / 1000000000) ≤ -Real.log (1157 / 25600) ∧
    -Real.log (1157 / 25600) ≤ (1548380953 / 500000000) := by
  have h := checkLog_sound (w := (443 / 2757)) (n := 12)
    (lo := (324173181 / 1000000000)) (hi := (162086591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1157) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1157) = 1/(1157 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1548380953 / 500000000) (-3096761901 / 1000000000) (Real.log (1157 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (341768071 / 500000000) ≤ -Real.log (100000 / 198087) ∧
    -Real.log (100000 / 198087) ≤ (683536143 / 1000000000) := by
  have h := checkLog_sound (w := (98087 / 298087)) (n := 12)
    (lo := (341768071 / 500000000)) (hi := (683536143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198087 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198087 / 100000) = 1/(100000 / 198087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (341768071 / 500000000) (683536143 / 1000000000) (Real.log (198087 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (198087 / 100000) = -Real.log (100000 / 198087) := by
    rw [show ((198087 / 100000) : ℝ) = ((100000 / 198087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (989124373 / 250000000) ≤ -Real.log (1913 / 100000) ∧
    -Real.log (1913 / 100000) ≤ (1978248749 / 500000000) := by
  have h := checkLog_sound (w := (606 / 2519)) (n := 12)
    (lo := (61345199 / 125000000)) (hi := (490761593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1913) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3125 / 1913) = 1/(1913 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1978248749 / 500000000) (-989124373 / 250000000) (Real.log (1913 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (683612873 / 1000000000) ≤ -Real.log (500000 / 990511) ∧
    -Real.log (500000 / 990511) ≤ (341806437 / 500000000) := by
  have h := checkLog_sound (w := (490511 / 1490511)) (n := 12)
    (lo := (683612873 / 1000000000)) (hi := (341806437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990511 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990511 / 500000) = 1/(500000 / 990511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (683612873 / 1000000000) (341806437 / 500000000) (Real.log (990511 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (990511 / 500000) = -Real.log (500000 / 990511) := by
    rw [show ((990511 / 500000) : ℝ) = ((500000 / 990511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1982237431 / 500000000) ≤ -Real.log (9489 / 500000) ∧
    -Real.log (9489 / 500000) ≤ (991118717 / 250000000) := by
  have h := checkLog_sound (w := (3068 / 12557)) (n := 12)
    (lo := (249369481 / 500000000)) (hi := (498738963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9489) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9489) = 1/(9489 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-991118717 / 250000000) (-1982237431 / 500000000) (Real.log (9489 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (2733981 / 4000000) ≤ -Real.log (1000000 / 1980789) ∧
    -Real.log (1000000 / 1980789) ≤ (683495251 / 1000000000) := by
  have h := checkLog_sound (w := (980789 / 2980789)) (n := 12)
    (lo := (2733981 / 4000000)) (hi := (683495251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980789 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980789 / 1000000) = 1/(1000000 / 1980789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (2733981 / 4000000) (683495251 / 1000000000) (Real.log (1980789 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1980789 / 1000000) = -Real.log (1000000 / 1980789) := by
    rw [show ((1980789 / 1000000) : ℝ) = ((1000000 / 1980789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (988068061 / 250000000) ≤ -Real.log (19211 / 1000000) ∧
    -Real.log (19211 / 1000000) ≤ (15809089 / 4000000) := by
  have h := checkLog_sound (w := (12039 / 50461)) (n := 12)
    (lo := (60817043 / 125000000)) (hi := (97307269 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19211) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19211) = 1/(19211 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-15809089 / 4000000) (-988068061 / 250000000) (Real.log (19211 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (683572993 / 1000000000) ≤ -Real.log (1000000 / 1980943) ∧
    -Real.log (1000000 / 1980943) ≤ (341786497 / 500000000) := by
  have h := checkLog_sound (w := (980943 / 2980943)) (n := 12)
    (lo := (683572993 / 1000000000)) (hi := (341786497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1980943 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1980943 / 1000000) = 1/(1000000 / 1980943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (683572993 / 1000000000) (341786497 / 500000000) (Real.log (1980943 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1980943 / 1000000) = -Real.log (1000000 / 1980943) := by
    rw [show ((1980943 / 1000000) : ℝ) = ((1000000 / 1980943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (990080197 / 250000000) ≤ -Real.log (19057 / 1000000) ∧
    -Real.log (19057 / 1000000) ≤ (1980160397 / 500000000) := by
  have h := checkLog_sound (w := (12193 / 50307)) (n := 12)
    (lo := (61823111 / 125000000)) (hi := (494584889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19057) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 19057) = 1/(19057 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1980160397 / 500000000) (-990080197 / 250000000) (Real.log (19057 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2320016817 / 500000000) ≤ -Real.log (500000000000 / 51773915316257) ∧
    -Real.log (500000000000 / 51773915316257) ≤ (4640033641 / 1000000000) := by
  have h := checkLog_sound (w := (19773915316257 / 83773915316257)) (n := 12)
    (lo := (240575277 / 500000000)) (hi := (96230111 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51773915316257 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(51773915316257 / 32000000000000) = 1/(500000000000 / 51773915316257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2320016817 / 500000000) (4640033641 / 1000000000) (Real.log (51773915316257 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (51773915316257 / 500000000000) = -Real.log (500000000000 / 51773915316257) := by
    rw [show ((51773915316257 / 500000000000) : ℝ) = ((500000000000 / 51773915316257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (929617547 / 200000000) ≤ -Real.log (500000000000 / 52192591421647) ∧
    -Real.log (500000000000 / 52192591421647) ≤ (2324043871 / 500000000) := by
  have h := checkLog_sound (w := (20192591421647 / 84192591421647)) (n := 12)
    (lo := (97840931 / 200000000)) (hi := (30575291 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52192591421647 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(52192591421647 / 32000000000000) = 1/(500000000000 / 52192591421647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (929617547 / 200000000) (2324043871 / 500000000) (Real.log (52192591421647 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (52192591421647 / 500000000000) = -Real.log (500000000000 / 52192591421647) := by
    rw [show ((52192591421647 / 500000000000) : ℝ) = ((500000000000 / 52192591421647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2317883747 / 500000000) ≤ -Real.log (500000000000 / 51553511009317) ∧
    -Real.log (500000000000 / 51553511009317) ≤ (4635767501 / 1000000000) := by
  have h := checkLog_sound (w := (19553511009317 / 83553511009317)) (n := 12)
    (lo := (238442207 / 500000000)) (hi := (95376883 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51553511009317 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(51553511009317 / 32000000000000) = 1/(500000000000 / 51553511009317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2317883747 / 500000000) (4635767501 / 1000000000) (Real.log (51553511009317 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (51553511009317 / 500000000000) = -Real.log (500000000000 / 51553511009317) := by
    rw [show ((51553511009317 / 500000000000) : ℝ) = ((500000000000 / 51553511009317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4643893781 / 1000000000) ≤ -Real.log (100000000000 / 10394831295587) ∧
    -Real.log (100000000000 / 10394831295587) ≤ (1160973447 / 250000000) := by
  have h := checkLog_sound (w := (3994831295587 / 16794831295587)) (n := 12)
    (lo := (485010701 / 1000000000)) (hi := (242505351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10394831295587 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(10394831295587 / 6400000000000) = 1/(100000000000 / 10394831295587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4643893781 / 1000000000) (1160973447 / 250000000) (Real.log (10394831295587 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (10394831295587 / 100000000000) = -Real.log (100000000000 / 10394831295587) := by
    rw [show ((10394831295587 / 100000000000) : ℝ) = ((100000000000 / 10394831295587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0020
