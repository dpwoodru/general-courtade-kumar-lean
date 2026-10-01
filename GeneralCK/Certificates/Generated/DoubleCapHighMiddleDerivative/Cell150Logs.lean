import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell150
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

theorem reflection_log_1_neg : (291532073 / 1000000000) ≤ -Real.log (5120 / 6853) ∧
    -Real.log (5120 / 6853) ≤ (145766037 / 500000000) := by
  have h := checkLog_sound (w := (1733 / 11973)) (n := 12)
    (lo := (291532073 / 1000000000)) (hi := (145766037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6853 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6853 / 5120) = 1/(5120 / 6853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (291532073 / 1000000000) (145766037 / 500000000) (Real.log (6853 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6853 / 5120) = -Real.log (5120 / 6853) := by
    rw [show ((6853 / 5120) : ℝ) = ((5120 / 6853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (82641973 / 200000000) ≤ -Real.log (3387 / 5120) ∧
    -Real.log (3387 / 5120) ≤ (206604933 / 500000000) := by
  have h := checkLog_sound (w := (1733 / 8507)) (n := 12)
    (lo := (82641973 / 200000000)) (hi := (206604933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3387) = 1/(3387 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-206604933 / 500000000) (-82641973 / 200000000) (Real.log (3387 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (291094213 / 1000000000) ≤ -Real.log (512 / 685) ∧
    -Real.log (512 / 685) ≤ (145547107 / 500000000) := by
  have h := checkLog_sound (w := (173 / 1197)) (n := 12)
    (lo := (291094213 / 1000000000)) (hi := (145547107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685 / 512) = 1/(512 / 685) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (291094213 / 1000000000) (145547107 / 500000000) (Real.log (685 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (685 / 512) = -Real.log (512 / 685) := by
    rw [show ((685 / 512) : ℝ) = ((512 / 685) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (412324517 / 1000000000) ≤ -Real.log (339 / 512) ∧
    -Real.log (339 / 512) ≤ (206162259 / 500000000) := by
  have h := checkLog_sound (w := (173 / 851)) (n := 12)
    (lo := (412324517 / 1000000000)) (hi := (206162259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 339) = 1/(339 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-206162259 / 500000000) (-412324517 / 1000000000) (Real.log (339 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (26900817 / 125000000) ≤ -Real.log (500000 / 620059) ∧
    -Real.log (500000 / 620059) ≤ (215206537 / 1000000000) := by
  have h := checkLog_sound (w := (120059 / 1120059)) (n := 12)
    (lo := (26900817 / 125000000)) (hi := (215206537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((620059 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(620059 / 500000) = 1/(500000 / 620059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (26900817 / 125000000) (215206537 / 1000000000) (Real.log (620059 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (620059 / 500000) = -Real.log (500000 / 620059) := by
    rw [show ((620059 / 500000) : ℝ) = ((500000 / 620059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (6864803 / 25000000) ≤ -Real.log (379941 / 500000) ∧
    -Real.log (379941 / 500000) ≤ (274592121 / 1000000000) := by
  have h := checkLog_sound (w := (120059 / 879941)) (n := 12)
    (lo := (6864803 / 25000000)) (hi := (274592121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 379941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 379941) = 1/(379941 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-274592121 / 1000000000) (-6864803 / 25000000) (Real.log (379941 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (13471673 / 62500000) ≤ -Real.log (50000 / 62027) ∧
    -Real.log (50000 / 62027) ≤ (215546769 / 1000000000) := by
  have h := checkLog_sound (w := (12027 / 112027)) (n := 12)
    (lo := (13471673 / 62500000)) (hi := (215546769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62027 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62027 / 50000) = 1/(50000 / 62027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (13471673 / 62500000) (215546769 / 1000000000) (Real.log (62027 / 50000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (62027 / 50000) = -Real.log (50000 / 62027) := by
    rw [show ((62027 / 50000) : ℝ) = ((50000 / 62027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (34393453 / 125000000) ≤ -Real.log (37973 / 50000) ∧
    -Real.log (37973 / 50000) ≤ (2201181 / 8000000) := by
  have h := checkLog_sound (w := (12027 / 87973)) (n := 12)
    (lo := (34393453 / 125000000)) (hi := (2201181 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 37973) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 37973) = 1/(37973 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2201181 / 8000000) (-34393453 / 125000000) (Real.log (37973 / 50000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (795883 / 5000000) ≤ -Real.log (200000 / 234509) ∧
    -Real.log (200000 / 234509) ≤ (159176601 / 1000000000) := by
  have h := checkLog_sound (w := (34509 / 434509)) (n := 12)
    (lo := (795883 / 5000000)) (hi := (159176601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((234509 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(234509 / 200000) = 1/(200000 / 234509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (795883 / 5000000) (159176601 / 1000000000) (Real.log (234509 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (234509 / 200000) = -Real.log (200000 / 234509) := by
    rw [show ((234509 / 200000) : ℝ) = ((200000 / 234509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (189400553 / 1000000000) ≤ -Real.log (165491 / 200000) ∧
    -Real.log (165491 / 200000) ≤ (94700277 / 500000000) := by
  have h := checkLog_sound (w := (34509 / 365491)) (n := 12)
    (lo := (189400553 / 1000000000)) (hi := (94700277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 165491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 165491) = 1/(165491 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-94700277 / 500000000) (-189400553 / 1000000000) (Real.log (165491 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (31888701 / 200000000) ≤ -Real.log (500000 / 586429) ∧
    -Real.log (500000 / 586429) ≤ (79721753 / 500000000) := by
  have h := checkLog_sound (w := (86429 / 1086429)) (n := 12)
    (lo := (31888701 / 200000000)) (hi := (79721753 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586429 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586429 / 500000) = 1/(500000 / 586429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (31888701 / 200000000) (79721753 / 500000000) (Real.log (586429 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (586429 / 500000) = -Real.log (500000 / 586429) := by
    rw [show ((586429 / 500000) : ℝ) = ((500000 / 586429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (189778893 / 1000000000) ≤ -Real.log (413571 / 500000) ∧
    -Real.log (413571 / 500000) ≤ (94889447 / 500000000) := by
  have h := checkLog_sound (w := (86429 / 913571)) (n := 12)
    (lo := (189778893 / 1000000000)) (hi := (94889447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 413571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 413571) = 1/(413571 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-94889447 / 500000000) (-189778893 / 1000000000) (Real.log (413571 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (70341873 / 100000000) ≤ -Real.log (20000000000 / 40412979351) ∧
    -Real.log (20000000000 / 40412979351) ≤ (175854683 / 250000000) := by
  have h := checkLog_sound (w := (412979351 / 80412979351)) (n := 12)
    (lo := (205431 / 20000000)) (hi := (10271551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40412979351 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40412979351 / 40000000000) = 1/(20000000000 / 40412979351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (70341873 / 100000000) (175854683 / 250000000) (Real.log (40412979351 / 20000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (40412979351 / 20000000000) = -Real.log (20000000000 / 40412979351) := by
    rw [show ((40412979351 / 20000000000) : ℝ) = ((20000000000 / 40412979351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (352370969 / 500000000) ≤ -Real.log (500000000000 / 1011662237969) ∧
    -Real.log (500000000000 / 1011662237969) ≤ (35237097 / 50000000) := by
  have h := checkLog_sound (w := (11662237969 / 2011662237969)) (n := 12)
    (lo := (5797379 / 500000000)) (hi := (11594759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1011662237969 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1011662237969 / 1000000000000) = 1/(500000000000 / 1011662237969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (352370969 / 500000000) (35237097 / 50000000) (Real.log (1011662237969 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1011662237969 / 500000000000) = -Real.log (500000000000 / 1011662237969) := by
    rw [show ((1011662237969 / 500000000000) : ℝ) = ((500000000000 / 1011662237969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (489798657 / 1000000000) ≤ -Real.log (500000000000 / 815993799037) ∧
    -Real.log (500000000000 / 815993799037) ≤ (244899329 / 500000000) := by
  have h := checkLog_sound (w := (315993799037 / 1315993799037)) (n := 12)
    (lo := (489798657 / 1000000000)) (hi := (244899329 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((815993799037 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(815993799037 / 500000000000) = 1/(500000000000 / 815993799037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (489798657 / 1000000000) (244899329 / 500000000) (Real.log (815993799037 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (815993799037 / 500000000000) = -Real.log (500000000000 / 815993799037) := by
    rw [show ((815993799037 / 500000000000) : ℝ) = ((500000000000 / 815993799037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (490694393 / 1000000000) ≤ -Real.log (500000000000 / 816725041477) ∧
    -Real.log (500000000000 / 816725041477) ≤ (245347197 / 500000000) := by
  have h := checkLog_sound (w := (316725041477 / 1316725041477)) (n := 12)
    (lo := (490694393 / 1000000000)) (hi := (245347197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((816725041477 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(816725041477 / 500000000000) = 1/(500000000000 / 816725041477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (490694393 / 1000000000) (245347197 / 500000000) (Real.log (816725041477 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (816725041477 / 500000000000) = -Real.log (500000000000 / 816725041477) := by
    rw [show ((816725041477 / 500000000000) : ℝ) = ((500000000000 / 816725041477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (174288577 / 500000000) ≤ -Real.log (50000000000 / 70852493489) ∧
    -Real.log (50000000000 / 70852493489) ≤ (69715431 / 200000000) := by
  have h := checkLog_sound (w := (20852493489 / 120852493489)) (n := 12)
    (lo := (174288577 / 500000000)) (hi := (69715431 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70852493489 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(70852493489 / 50000000000) = 1/(50000000000 / 70852493489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (174288577 / 500000000) (69715431 / 200000000) (Real.log (70852493489 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (70852493489 / 50000000000) = -Real.log (50000000000 / 70852493489) := by
    rw [show ((70852493489 / 50000000000) : ℝ) = ((50000000000 / 70852493489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (174611199 / 500000000) ≤ -Real.log (500000000000 / 708982254559) ∧
    -Real.log (500000000000 / 708982254559) ≤ (349222399 / 1000000000) := by
  have h := checkLog_sound (w := (208982254559 / 1208982254559)) (n := 12)
    (lo := (174611199 / 500000000)) (hi := (349222399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((708982254559 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(708982254559 / 500000000000) = 1/(500000000000 / 708982254559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (174611199 / 500000000) (349222399 / 1000000000) (Real.log (708982254559 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (708982254559 / 500000000000) = -Real.log (500000000000 / 708982254559) := by
    rw [show ((708982254559 / 500000000000) : ℝ) = ((500000000000 / 708982254559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (7583847 / 250000000) ≤ -Real.log (242530027959 / 250000000000) ∧
    -Real.log (242530027959 / 250000000000) ≤ (30335389 / 1000000000) := by
  have h := checkLog_sound (w := (7469972041 / 492530027959)) (n := 12)
    (lo := (7583847 / 250000000)) (hi := (30335389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242530027959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242530027959) = 1/(242530027959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-30335389 / 1000000000) (-7583847 / 250000000) (Real.log (242530027959 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (30223953 / 1000000000) ≤ -Real.log (38809128919 / 40000000000) ∧
    -Real.log (38809128919 / 40000000000) ≤ (15111977 / 500000000) := by
  have h := checkLog_sound (w := (1190871081 / 78809128919)) (n := 12)
    (lo := (30223953 / 1000000000)) (hi := (15111977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38809128919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38809128919) = 1/(38809128919 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-15111977 / 500000000) (-30223953 / 1000000000) (Real.log (38809128919 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell150
