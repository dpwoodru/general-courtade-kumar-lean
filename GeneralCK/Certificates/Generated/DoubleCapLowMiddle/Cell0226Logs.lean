import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0226
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

theorem reflection_log_1_neg : (484738289 / 1000000000) ≤ -Real.log (800 / 1299) ∧
    -Real.log (800 / 1299) ≤ (48473829 / 100000000) := by
  have h := checkLog_sound (w := (499 / 2099)) (n := 12)
    (lo := (484738289 / 1000000000)) (hi := (48473829 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1299 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1299 / 800) = 1/(800 / 1299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (484738289 / 1000000000) (48473829 / 100000000) (Real.log (1299 / 800)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1299 / 800) = -Real.log (800 / 1299) := by
    rw [show ((1299 / 800) : ℝ) = ((800 / 1299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (488750731 / 500000000) ≤ -Real.log (301 / 800) ∧
    -Real.log (301 / 800) ≤ (122187683 / 125000000) := by
  have h := checkLog_sound (w := (99 / 701)) (n := 12)
    (lo := (142177141 / 500000000)) (hi := (284354283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 301) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 301) = 1/(301 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-122187683 / 125000000) (-488750731 / 500000000) (Real.log (301 / 800)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (477398097 / 1000000000) ≤ -Real.log (1600 / 2579) ∧
    -Real.log (1600 / 2579) ≤ (238699049 / 500000000) := by
  have h := checkLog_sound (w := (979 / 4179)) (n := 12)
    (lo := (477398097 / 1000000000)) (hi := (238699049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2579 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2579 / 1600) = 1/(1600 / 2579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (477398097 / 1000000000) (238699049 / 500000000) (Real.log (2579 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2579 / 1600) = -Real.log (1600 / 2579) := by
    rw [show ((2579 / 1600) : ℝ) = ((1600 / 2579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (37857113 / 40000000) ≤ -Real.log (621 / 1600) ∧
    -Real.log (621 / 1600) ≤ (946427827 / 1000000000) := by
  have h := checkLog_sound (w := (179 / 1421)) (n := 12)
    (lo := (50656129 / 200000000)) (hi := (126640323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 621) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 621) = 1/(621 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-946427827 / 1000000000) (-37857113 / 40000000) (Real.log (621 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (55285387 / 250000000) ≤ -Real.log (400 / 499) ∧
    -Real.log (400 / 499) ≤ (221141549 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 899)) (n := 12)
    (lo := (55285387 / 250000000)) (hi := (221141549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((499 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(499 / 400) = 1/(400 / 499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (55285387 / 250000000) (221141549 / 1000000000) (Real.log (499 / 400)) := by
  have h := reflection_log_5_neg
  have he : Real.log (499 / 400) = -Real.log (400 / 499) := by
    rw [show ((499 / 400) : ℝ) = ((400 / 499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (142177141 / 500000000) ≤ -Real.log (301 / 400) ∧
    -Real.log (301 / 400) ≤ (284354283 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 701)) (n := 12)
    (lo := (142177141 / 500000000)) (hi := (284354283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 301) = 1/(301 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-284354283 / 1000000000) (-142177141 / 500000000) (Real.log (301 / 400)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (100959957 / 500000000) ≤ -Real.log (800 / 979) ∧
    -Real.log (800 / 979) ≤ (40383983 / 200000000) := by
  have h := checkLog_sound (w := (179 / 1779)) (n := 12)
    (lo := (100959957 / 500000000)) (hi := (40383983 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((979 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(979 / 800) = 1/(800 / 979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (100959957 / 500000000) (40383983 / 200000000) (Real.log (979 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (979 / 800) = -Real.log (800 / 979) := by
    rw [show ((979 / 800) : ℝ) = ((800 / 979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (50656129 / 200000000) ≤ -Real.log (621 / 800) ∧
    -Real.log (621 / 800) ≤ (126640323 / 500000000) := by
  have h := checkLog_sound (w := (179 / 1421)) (n := 12)
    (lo := (50656129 / 200000000)) (hi := (126640323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800 / 621) = 1/(621 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-126640323 / 500000000) (-50656129 / 200000000) (Real.log (621 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (583245257 / 1000000000) ≤ -Real.log (250000 / 447961) ∧
    -Real.log (250000 / 447961) ≤ (291622629 / 500000000) := by
  have h := checkLog_sound (w := (197961 / 697961)) (n := 12)
    (lo := (583245257 / 1000000000)) (hi := (291622629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((447961 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(447961 / 250000) = 1/(250000 / 447961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (583245257 / 1000000000) (291622629 / 500000000) (Real.log (447961 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (447961 / 250000) = -Real.log (250000 / 447961) := by
    rw [show ((447961 / 250000) : ℝ) = ((250000 / 447961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1569467479 / 1000000000) ≤ -Real.log (52039 / 250000) ∧
    -Real.log (52039 / 250000) ≤ (784733741 / 500000000) := by
  have h := checkLog_sound (w := (10461 / 114539)) (n := 12)
    (lo := (183173119 / 1000000000)) (hi := (71552 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 52039) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(62500 / 52039) = 1/(52039 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-784733741 / 500000000) (-1569467479 / 1000000000) (Real.log (52039 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (584718629 / 1000000000) ≤ -Real.log (500000 / 897243) ∧
    -Real.log (500000 / 897243) ≤ (58471863 / 100000000) := by
  have h := checkLog_sound (w := (397243 / 1397243)) (n := 12)
    (lo := (584718629 / 1000000000)) (hi := (58471863 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((897243 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(897243 / 500000) = 1/(500000 / 897243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (584718629 / 1000000000) (58471863 / 100000000) (Real.log (897243 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (897243 / 500000) = -Real.log (500000 / 897243) := by
    rw [show ((897243 / 500000) : ℝ) = ((500000 / 897243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1582241119 / 1000000000) ≤ -Real.log (102757 / 500000) ∧
    -Real.log (102757 / 500000) ≤ (791120561 / 500000000) := by
  have h := checkLog_sound (w := (22243 / 227757)) (n := 12)
    (lo := (195946759 / 1000000000)) (hi := (4898669 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 102757) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 102757) = 1/(102757 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-791120561 / 500000000) (-1582241119 / 1000000000) (Real.log (102757 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (273542227 / 500000000) ≤ -Real.log (1000000 / 1728207) ∧
    -Real.log (1000000 / 1728207) ≤ (109416891 / 200000000) := by
  have h := checkLog_sound (w := (728207 / 2728207)) (n := 12)
    (lo := (273542227 / 500000000)) (hi := (109416891 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1728207 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1728207 / 1000000) = 1/(1000000 / 1728207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (273542227 / 500000000) (109416891 / 200000000) (Real.log (1728207 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1728207 / 1000000) = -Real.log (1000000 / 1728207) := by
    rw [show ((1728207 / 1000000) : ℝ) = ((1000000 / 1728207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1302714531 / 1000000000) ≤ -Real.log (271793 / 1000000) ∧
    -Real.log (271793 / 1000000) ≤ (1302714533 / 1000000000) := by
  have h := checkLog_sound (w := (228207 / 771793)) (n := 12)
    (lo := (609567351 / 1000000000)) (hi := (76195919 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 271793) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 271793) = 1/(271793 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1302714533 / 1000000000) (-1302714531 / 1000000000) (Real.log (271793 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (110276627 / 200000000) ≤ -Real.log (250000 / 433913) ∧
    -Real.log (250000 / 433913) ≤ (17230723 / 31250000) := by
  have h := checkLog_sound (w := (183913 / 683913)) (n := 12)
    (lo := (110276627 / 200000000)) (hi := (17230723 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((433913 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(433913 / 250000) = 1/(250000 / 433913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (110276627 / 200000000) (17230723 / 31250000) (Real.log (433913 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (433913 / 250000) = -Real.log (250000 / 433913) := by
    rw [show ((433913 / 250000) : ℝ) = ((250000 / 433913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1330488861 / 1000000000) ≤ -Real.log (66087 / 250000) ∧
    -Real.log (66087 / 250000) ≤ (1330488863 / 1000000000) := by
  have h := checkLog_sound (w := (58913 / 191087)) (n := 12)
    (lo := (637341681 / 1000000000)) (hi := (318670841 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 66087) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 66087) = 1/(66087 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1330488863 / 1000000000) (-1330488861 / 1000000000) (Real.log (66087 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (430542547 / 200000000) ≤ -Real.log (500000000000 / 4304089240761) ∧
    -Real.log (500000000000 / 4304089240761) ≤ (2152712739 / 1000000000) := by
  have h := checkLog_sound (w := (304089240761 / 8304089240761)) (n := 12)
    (lo := (14654239 / 200000000)) (hi := (18317799 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4304089240761 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4304089240761 / 4000000000000) = 1/(500000000000 / 4304089240761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (430542547 / 200000000) (2152712739 / 1000000000) (Real.log (4304089240761 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4304089240761 / 500000000000) = -Real.log (500000000000 / 4304089240761) := by
    rw [show ((4304089240761 / 500000000000) : ℝ) = ((500000000000 / 4304089240761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2166959749 / 1000000000) ≤ -Real.log (50000000000 / 436584855533) ∧
    -Real.log (50000000000 / 436584855533) ≤ (2166959753 / 1000000000) := by
  have h := checkLog_sound (w := (36584855533 / 836584855533)) (n := 12)
    (lo := (87518209 / 1000000000)) (hi := (8751821 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((436584855533 / 400000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(436584855533 / 400000000000) = 1/(50000000000 / 436584855533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2166959749 / 1000000000) (2166959753 / 1000000000) (Real.log (436584855533 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (436584855533 / 50000000000) = -Real.log (50000000000 / 436584855533) := by
    rw [show ((436584855533 / 50000000000) : ℝ) = ((50000000000 / 436584855533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (369959797 / 200000000) ≤ -Real.log (31250000000 / 198704413837) ∧
    -Real.log (31250000000 / 198704413837) ≤ (462449747 / 250000000) := by
  have h := checkLog_sound (w := (73704413837 / 323704413837)) (n := 12)
    (lo := (3708037 / 8000000)) (hi := (231752313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198704413837 / 125000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(198704413837 / 125000000000) = 1/(31250000000 / 198704413837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (369959797 / 200000000) (462449747 / 250000000) (Real.log (198704413837 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (198704413837 / 31250000000) = -Real.log (31250000000 / 198704413837) := by
    rw [show ((198704413837 / 31250000000) : ℝ) = ((31250000000 / 198704413837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (470467999 / 250000000) ≤ -Real.log (250000000000 / 1641446124049) ∧
    -Real.log (250000000000 / 1641446124049) ≤ (1881871999 / 1000000000) := by
  have h := checkLog_sound (w := (641446124049 / 2641446124049)) (n := 12)
    (lo := (123894409 / 250000000)) (hi := (495577637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1641446124049 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1641446124049 / 1000000000000) = 1/(250000000000 / 1641446124049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (470467999 / 250000000) (1881871999 / 1000000000) (Real.log (1641446124049 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1641446124049 / 250000000000) = -Real.log (250000000000 / 1641446124049) := by
    rw [show ((1641446124049 / 250000000000) : ℝ) = ((250000000000 / 1641446124049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0226
