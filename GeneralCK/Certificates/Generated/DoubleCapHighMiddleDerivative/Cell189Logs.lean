import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell189
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

theorem reflection_log_1_neg : (61692157 / 200000000) ≤ -Real.log (512 / 697) ∧
    -Real.log (512 / 697) ≤ (154230393 / 500000000) := by
  have h := checkLog_sound (w := (185 / 1209)) (n := 12)
    (lo := (61692157 / 200000000)) (hi := (154230393 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697 / 512) = 1/(512 / 697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (61692157 / 200000000) (154230393 / 500000000) (Real.log (697 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (697 / 512) = -Real.log (512 / 697) := by
    rw [show ((697 / 512) : ℝ) = ((512 / 697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (224182227 / 500000000) ≤ -Real.log (327 / 512) ∧
    -Real.log (327 / 512) ≤ (89672891 / 200000000) := by
  have h := checkLog_sound (w := (185 / 839)) (n := 12)
    (lo := (224182227 / 500000000)) (hi := (89672891 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 327) = 1/(327 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-89672891 / 200000000) (-224182227 / 500000000) (Real.log (327 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (77007569 / 250000000) ≤ -Real.log (5120 / 6967) ∧
    -Real.log (5120 / 6967) ≤ (308030277 / 1000000000) := by
  have h := checkLog_sound (w := (1847 / 12087)) (n := 12)
    (lo := (77007569 / 250000000)) (hi := (308030277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6967 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6967 / 5120) = 1/(5120 / 6967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (77007569 / 250000000) (308030277 / 1000000000) (Real.log (6967 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6967 / 5120) = -Real.log (5120 / 6967) := by
    rw [show ((6967 / 5120) : ℝ) = ((5120 / 6967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (447447443 / 1000000000) ≤ -Real.log (3273 / 5120) ∧
    -Real.log (3273 / 5120) ≤ (111861861 / 250000000) := by
  have h := checkLog_sound (w := (1847 / 8393)) (n := 12)
    (lo := (447447443 / 1000000000)) (hi := (111861861 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3273) = 1/(3273 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-111861861 / 250000000) (-447447443 / 1000000000) (Real.log (3273 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (114183343 / 500000000) ≤ -Real.log (500000 / 628273) ∧
    -Real.log (500000 / 628273) ≤ (228366687 / 1000000000) := by
  have h := checkLog_sound (w := (128273 / 1128273)) (n := 12)
    (lo := (114183343 / 500000000)) (hi := (228366687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((628273 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(628273 / 500000) = 1/(500000 / 628273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (114183343 / 500000000) (228366687 / 1000000000) (Real.log (628273 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (628273 / 500000) = -Real.log (500000 / 628273) := by
    rw [show ((628273 / 500000) : ℝ) = ((500000 / 628273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2316003 / 7812500) ≤ -Real.log (371727 / 500000) ∧
    -Real.log (371727 / 500000) ≤ (59289677 / 200000000) := by
  have h := checkLog_sound (w := (128273 / 871727)) (n := 12)
    (lo := (2316003 / 7812500)) (hi := (59289677 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 371727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 371727) = 1/(371727 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-59289677 / 200000000) (-2316003 / 7812500) (Real.log (371727 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (228703267 / 1000000000) ≤ -Real.log (1000000 / 1256969) ∧
    -Real.log (1000000 / 1256969) ≤ (57175817 / 250000000) := by
  have h := checkLog_sound (w := (256969 / 2256969)) (n := 12)
    (lo := (228703267 / 1000000000)) (hi := (57175817 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1256969 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1256969 / 1000000) = 1/(1000000 / 1256969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (228703267 / 1000000000) (57175817 / 250000000) (Real.log (1256969 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1256969 / 1000000) = -Real.log (1000000 / 1256969) := by
    rw [show ((1256969 / 1000000) : ℝ) = ((1000000 / 1256969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (37127189 / 125000000) ≤ -Real.log (743031 / 1000000) ∧
    -Real.log (743031 / 1000000) ≤ (297017513 / 1000000000) := by
  have h := checkLog_sound (w := (256969 / 1743031)) (n := 12)
    (lo := (37127189 / 125000000)) (hi := (297017513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 743031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 743031) = 1/(743031 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-297017513 / 1000000000) (-37127189 / 125000000) (Real.log (743031 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (169552039 / 1000000000) ≤ -Real.log (500000 / 592387) ∧
    -Real.log (500000 / 592387) ≤ (4238801 / 25000000) := by
  have h := checkLog_sound (w := (92387 / 1092387)) (n := 12)
    (lo := (169552039 / 1000000000)) (hi := (4238801 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592387 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592387 / 500000) = 1/(500000 / 592387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (169552039 / 1000000000) (4238801 / 25000000) (Real.log (592387 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (592387 / 500000) = -Real.log (500000 / 592387) := by
    rw [show ((592387 / 500000) : ℝ) = ((500000 / 592387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (204289903 / 1000000000) ≤ -Real.log (407613 / 500000) ∧
    -Real.log (407613 / 500000) ≤ (12768119 / 62500000) := by
  have h := checkLog_sound (w := (92387 / 907613)) (n := 12)
    (lo := (204289903 / 1000000000)) (hi := (12768119 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 407613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 407613) = 1/(407613 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-12768119 / 62500000) (-204289903 / 1000000000) (Real.log (407613 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (169818721 / 1000000000) ≤ -Real.log (100000 / 118509) ∧
    -Real.log (100000 / 118509) ≤ (84909361 / 500000000) := by
  have h := checkLog_sound (w := (18509 / 218509)) (n := 12)
    (lo := (169818721 / 1000000000)) (hi := (84909361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118509 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118509 / 100000) = 1/(100000 / 118509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (169818721 / 1000000000) (84909361 / 500000000) (Real.log (118509 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (118509 / 100000) = -Real.log (100000 / 118509) := by
    rw [show ((118509 / 100000) : ℝ) = ((100000 / 118509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (204677601 / 1000000000) ≤ -Real.log (81491 / 100000) ∧
    -Real.log (81491 / 100000) ≤ (102338801 / 500000000) := by
  have h := checkLog_sound (w := (18509 / 181491)) (n := 12)
    (lo := (204677601 / 1000000000)) (hi := (102338801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 81491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 81491) = 1/(81491 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-102338801 / 500000000) (-204677601 / 1000000000) (Real.log (81491 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (755477719 / 1000000000) ≤ -Real.log (500000000000 / 1064314084937) ∧
    -Real.log (500000000000 / 1064314084937) ≤ (755477721 / 1000000000) := by
  have h := checkLog_sound (w := (64314084937 / 2064314084937)) (n := 12)
    (lo := (62330539 / 1000000000)) (hi := (3116527 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1064314084937 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1064314084937 / 1000000000000) = 1/(500000000000 / 1064314084937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (755477719 / 1000000000) (755477721 / 1000000000) (Real.log (1064314084937 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1064314084937 / 500000000000) = -Real.log (500000000000 / 1064314084937) := by
    rw [show ((1064314084937 / 500000000000) : ℝ) = ((500000000000 / 1064314084937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (756825239 / 1000000000) ≤ -Real.log (20000000000 / 42629969419) ∧
    -Real.log (20000000000 / 42629969419) ≤ (756825241 / 1000000000) := by
  have h := checkLog_sound (w := (2629969419 / 82629969419)) (n := 12)
    (lo := (63678059 / 1000000000)) (hi := (3183903 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42629969419 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(42629969419 / 40000000000) = 1/(20000000000 / 42629969419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (756825239 / 1000000000) (756825241 / 1000000000) (Real.log (42629969419 / 20000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (42629969419 / 20000000000) = -Real.log (20000000000 / 42629969419) := by
    rw [show ((42629969419 / 20000000000) : ℝ) = ((20000000000 / 42629969419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (524815071 / 1000000000) ≤ -Real.log (250000000000 / 422536565813) ∧
    -Real.log (250000000000 / 422536565813) ≤ (16400471 / 31250000) := by
  have h := checkLog_sound (w := (172536565813 / 672536565813)) (n := 12)
    (lo := (524815071 / 1000000000)) (hi := (16400471 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((422536565813 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(422536565813 / 250000000000) = 1/(250000000000 / 422536565813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (524815071 / 1000000000) (16400471 / 31250000) (Real.log (422536565813 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (422536565813 / 250000000000) = -Real.log (250000000000 / 422536565813) := by
    rw [show ((422536565813 / 250000000000) : ℝ) = ((250000000000 / 422536565813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (525720779 / 1000000000) ≤ -Real.log (3906250000 / 6608116157) ∧
    -Real.log (3906250000 / 6608116157) ≤ (26286039 / 50000000) := by
  have h := checkLog_sound (w := (2701866157 / 10514366157)) (n := 12)
    (lo := (525720779 / 1000000000)) (hi := (26286039 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6608116157 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6608116157 / 3906250000) = 1/(3906250000 / 6608116157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (525720779 / 1000000000) (26286039 / 50000000) (Real.log (6608116157 / 3906250000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (6608116157 / 3906250000) = -Real.log (3906250000 / 6608116157) := by
    rw [show ((6608116157 / 3906250000) : ℝ) = ((3906250000 / 6608116157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (186920971 / 500000000) ≤ -Real.log (500000000000 / 726653713203) ∧
    -Real.log (500000000000 / 726653713203) ≤ (373841943 / 1000000000) := by
  have h := checkLog_sound (w := (226653713203 / 1226653713203)) (n := 12)
    (lo := (186920971 / 500000000)) (hi := (373841943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((726653713203 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(726653713203 / 500000000000) = 1/(500000000000 / 726653713203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (186920971 / 500000000) (373841943 / 1000000000) (Real.log (726653713203 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (726653713203 / 500000000000) = -Real.log (500000000000 / 726653713203) := by
    rw [show ((726653713203 / 500000000000) : ℝ) = ((500000000000 / 726653713203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (187248161 / 500000000) ≤ -Real.log (500000000000 / 727129376251) ∧
    -Real.log (500000000000 / 727129376251) ≤ (374496323 / 1000000000) := by
  have h := checkLog_sound (w := (227129376251 / 1227129376251)) (n := 12)
    (lo := (187248161 / 500000000)) (hi := (374496323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727129376251 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727129376251 / 500000000000) = 1/(500000000000 / 727129376251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (187248161 / 500000000) (374496323 / 1000000000) (Real.log (727129376251 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (727129376251 / 500000000000) = -Real.log (500000000000 / 727129376251) := by
    rw [show ((727129376251 / 500000000000) : ℝ) = ((500000000000 / 727129376251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (54467 / 1562500) ≤ -Real.log (9657416919 / 10000000000) ∧
    -Real.log (9657416919 / 10000000000) ≤ (34858881 / 1000000000) := by
  have h := checkLog_sound (w := (342583081 / 19657416919)) (n := 12)
    (lo := (54467 / 1562500)) (hi := (34858881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9657416919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9657416919) = 1/(9657416919 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-34858881 / 1000000000) (-54467 / 1562500) (Real.log (9657416919 / 10000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (4342233 / 125000000) ≤ -Real.log (241464642231 / 250000000000) ∧
    -Real.log (241464642231 / 250000000000) ≤ (6947573 / 200000000) := by
  have h := checkLog_sound (w := (8535357769 / 491464642231)) (n := 12)
    (lo := (4342233 / 125000000)) (hi := (6947573 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241464642231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241464642231) = 1/(241464642231 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-6947573 / 200000000) (-4342233 / 125000000) (Real.log (241464642231 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell189
