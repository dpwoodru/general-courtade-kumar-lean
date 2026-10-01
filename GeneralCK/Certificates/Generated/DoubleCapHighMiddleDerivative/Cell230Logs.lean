import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell230
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (325953943 / 1000000000) ≤ -Real.log (5120 / 7093) ∧
    -Real.log (5120 / 7093) ≤ (40744243 / 125000000) := by
  have h := checkLog_sound (w := (1973 / 12213)) (n := 12)
    (lo := (325953943 / 1000000000)) (hi := (40744243 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7093 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7093 / 5120) = 1/(5120 / 7093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (325953943 / 1000000000) (40744243 / 125000000) (Real.log (7093 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7093 / 5120) = -Real.log (5120 / 7093) := by
    rw [show ((7093 / 5120) : ℝ) = ((5120 / 7093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (24335241 / 50000000) ≤ -Real.log (3147 / 5120) ∧
    -Real.log (3147 / 5120) ≤ (486704821 / 1000000000) := by
  have h := checkLog_sound (w := (1973 / 8267)) (n := 12)
    (lo := (24335241 / 50000000)) (hi := (486704821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3147) = 1/(3147 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-486704821 / 1000000000) (-24335241 / 50000000) (Real.log (3147 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (325530901 / 1000000000) ≤ -Real.log (512 / 709) ∧
    -Real.log (512 / 709) ≤ (162765451 / 500000000) := by
  have h := checkLog_sound (w := (197 / 1221)) (n := 12)
    (lo := (325530901 / 1000000000)) (hi := (162765451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((709 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(709 / 512) = 1/(512 / 709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (325530901 / 1000000000) (162765451 / 500000000) (Real.log (709 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (709 / 512) = -Real.log (512 / 709) := by
    rw [show ((709 / 512) : ℝ) = ((512 / 709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (242875993 / 500000000) ≤ -Real.log (315 / 512) ∧
    -Real.log (315 / 512) ≤ (485751987 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 827)) (n := 12)
    (lo := (242875993 / 500000000)) (hi := (485751987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 315) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 315) = 1/(315 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-485751987 / 1000000000) (-242875993 / 500000000) (Real.log (315 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (242051661 / 1000000000) ≤ -Real.log (50000 / 63693) ∧
    -Real.log (50000 / 63693) ≤ (121025831 / 500000000) := by
  have h := checkLog_sound (w := (13693 / 113693)) (n := 12)
    (lo := (242051661 / 1000000000)) (hi := (121025831 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63693 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63693 / 50000) = 1/(50000 / 63693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (242051661 / 1000000000) (121025831 / 500000000) (Real.log (63693 / 50000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (63693 / 50000) = -Real.log (50000 / 63693) := by
    rw [show ((63693 / 50000) : ℝ) = ((50000 / 63693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (64002489 / 200000000) ≤ -Real.log (36307 / 50000) ∧
    -Real.log (36307 / 50000) ≤ (160006223 / 500000000) := by
  have h := checkLog_sound (w := (13693 / 86307)) (n := 12)
    (lo := (64002489 / 200000000)) (hi := (160006223 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 36307) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 36307) = 1/(36307 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-160006223 / 500000000) (-64002489 / 200000000) (Real.log (36307 / 50000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (60596113 / 250000000) ≤ -Real.log (250000 / 318571) ∧
    -Real.log (250000 / 318571) ≤ (242384453 / 1000000000) := by
  have h := checkLog_sound (w := (68571 / 568571)) (n := 12)
    (lo := (60596113 / 250000000)) (hi := (242384453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((318571 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(318571 / 250000) = 1/(250000 / 318571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (60596113 / 250000000) (242384453 / 1000000000) (Real.log (318571 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (318571 / 250000) = -Real.log (250000 / 318571) := by
    rw [show ((318571 / 250000) : ℝ) = ((250000 / 318571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (12823861 / 40000000) ≤ -Real.log (181429 / 250000) ∧
    -Real.log (181429 / 250000) ≤ (160298263 / 500000000) := by
  have h := checkLog_sound (w := (68571 / 431429)) (n := 12)
    (lo := (12823861 / 40000000)) (hi := (160298263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 181429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 181429) = 1/(181429 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-160298263 / 500000000) (-12823861 / 40000000) (Real.log (181429 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (90224903 / 500000000) ≤ -Real.log (250000 / 299439) ∧
    -Real.log (250000 / 299439) ≤ (180449807 / 1000000000) := by
  have h := checkLog_sound (w := (49439 / 549439)) (n := 12)
    (lo := (90224903 / 500000000)) (hi := (180449807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299439 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299439 / 250000) = 1/(250000 / 299439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (90224903 / 500000000) (180449807 / 1000000000) (Real.log (299439 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (299439 / 250000) = -Real.log (250000 / 299439) := by
    rw [show ((299439 / 250000) : ℝ) = ((250000 / 299439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (220342477 / 1000000000) ≤ -Real.log (200561 / 250000) ∧
    -Real.log (200561 / 250000) ≤ (110171239 / 500000000) := by
  have h := checkLog_sound (w := (49439 / 450561)) (n := 12)
    (lo := (220342477 / 1000000000)) (hi := (110171239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 200561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 200561) = 1/(200561 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-110171239 / 500000000) (-220342477 / 1000000000) (Real.log (200561 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (90358051 / 500000000) ≤ -Real.log (40000 / 47923) ∧
    -Real.log (40000 / 47923) ≤ (180716103 / 1000000000) := by
  have h := checkLog_sound (w := (7923 / 87923)) (n := 12)
    (lo := (90358051 / 500000000)) (hi := (180716103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47923 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47923 / 40000) = 1/(40000 / 47923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (90358051 / 500000000) (180716103 / 1000000000) (Real.log (47923 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (47923 / 40000) = -Real.log (40000 / 47923) := by
    rw [show ((47923 / 40000) : ℝ) = ((40000 / 47923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (220740191 / 1000000000) ≤ -Real.log (32077 / 40000) ∧
    -Real.log (32077 / 40000) ≤ (6898131 / 31250000) := by
  have h := checkLog_sound (w := (7923 / 72077)) (n := 12)
    (lo := (220740191 / 1000000000)) (hi := (6898131 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 32077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 32077) = 1/(32077 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-6898131 / 31250000) (-220740191 / 1000000000) (Real.log (32077 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (811282887 / 1000000000) ≤ -Real.log (125000000000 / 281349206349) ∧
    -Real.log (125000000000 / 281349206349) ≤ (811282889 / 1000000000) := by
  have h := checkLog_sound (w := (31349206349 / 531349206349)) (n := 12)
    (lo := (118135707 / 1000000000)) (hi := (29533927 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((281349206349 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(281349206349 / 250000000000) = 1/(125000000000 / 281349206349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (811282887 / 1000000000) (811282889 / 1000000000) (Real.log (281349206349 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (281349206349 / 125000000000) = -Real.log (125000000000 / 281349206349) := by
    rw [show ((281349206349 / 125000000000) : ℝ) = ((125000000000 / 281349206349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (812658763 / 1000000000) ≤ -Real.log (250000000000 / 563473149031) ∧
    -Real.log (250000000000 / 563473149031) ≤ (162531753 / 200000000) := by
  have h := checkLog_sound (w := (63473149031 / 1063473149031)) (n := 12)
    (lo := (119511583 / 1000000000)) (hi := (3734737 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((563473149031 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(563473149031 / 500000000000) = 1/(250000000000 / 563473149031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (812658763 / 1000000000) (162531753 / 200000000) (Real.log (563473149031 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (563473149031 / 250000000000) = -Real.log (250000000000 / 563473149031) := by
    rw [show ((563473149031 / 250000000000) : ℝ) = ((250000000000 / 563473149031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (281032053 / 500000000) ≤ -Real.log (250000000000 / 438572451593) ∧
    -Real.log (250000000000 / 438572451593) ≤ (562064107 / 1000000000) := by
  have h := checkLog_sound (w := (188572451593 / 688572451593)) (n := 12)
    (lo := (281032053 / 500000000)) (hi := (562064107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((438572451593 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(438572451593 / 250000000000) = 1/(250000000000 / 438572451593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (281032053 / 500000000) (562064107 / 1000000000) (Real.log (438572451593 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (438572451593 / 250000000000) = -Real.log (250000000000 / 438572451593) := by
    rw [show ((438572451593 / 250000000000) : ℝ) = ((250000000000 / 438572451593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (562980977 / 1000000000) ≤ -Real.log (500000000000 / 877949500907) ∧
    -Real.log (500000000000 / 877949500907) ≤ (281490489 / 500000000) := by
  have h := checkLog_sound (w := (377949500907 / 1377949500907)) (n := 12)
    (lo := (562980977 / 1000000000)) (hi := (281490489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((877949500907 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(877949500907 / 500000000000) = 1/(500000000000 / 877949500907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (562980977 / 1000000000) (281490489 / 500000000) (Real.log (877949500907 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (877949500907 / 500000000000) = -Real.log (500000000000 / 877949500907) := by
    rw [show ((877949500907 / 500000000000) : ℝ) = ((500000000000 / 877949500907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (100198071 / 250000000) ≤ -Real.log (500000000000 / 746503557521) ∧
    -Real.log (500000000000 / 746503557521) ≤ (80158457 / 200000000) := by
  have h := checkLog_sound (w := (246503557521 / 1246503557521)) (n := 12)
    (lo := (100198071 / 250000000)) (hi := (80158457 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746503557521 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746503557521 / 500000000000) = 1/(500000000000 / 746503557521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (100198071 / 250000000) (80158457 / 200000000) (Real.log (746503557521 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (746503557521 / 500000000000) = -Real.log (500000000000 / 746503557521) := by
    rw [show ((746503557521 / 500000000000) : ℝ) = ((500000000000 / 746503557521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (401456293 / 1000000000) ≤ -Real.log (125000000000 / 186749851919) ∧
    -Real.log (125000000000 / 186749851919) ≤ (200728147 / 500000000) := by
  have h := checkLog_sound (w := (61749851919 / 311749851919)) (n := 12)
    (lo := (401456293 / 1000000000)) (hi := (200728147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((186749851919 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(186749851919 / 125000000000) = 1/(125000000000 / 186749851919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (401456293 / 1000000000) (200728147 / 500000000) (Real.log (186749851919 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (186749851919 / 125000000000) = -Real.log (125000000000 / 186749851919) := by
    rw [show ((186749851919 / 125000000000) : ℝ) = ((125000000000 / 186749851919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (40024089 / 1000000000) ≤ -Real.log (1537226071 / 1600000000) ∧
    -Real.log (1537226071 / 1600000000) ≤ (4002409 / 100000000) := by
  have h := checkLog_sound (w := (62773929 / 3137226071)) (n := 12)
    (lo := (40024089 / 1000000000)) (hi := (4002409 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1537226071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1537226071) = 1/(1537226071 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4002409 / 100000000) (-40024089 / 1000000000) (Real.log (1537226071 / 1600000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (39892671 / 1000000000) ≤ -Real.log (60055785279 / 62500000000) ∧
    -Real.log (60055785279 / 62500000000) ≤ (623323 / 15625000) := by
  have h := checkLog_sound (w := (2444214721 / 122555785279)) (n := 12)
    (lo := (39892671 / 1000000000)) (hi := (623323 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60055785279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60055785279) = 1/(60055785279 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-623323 / 15625000) (-39892671 / 1000000000) (Real.log (60055785279 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell230
