import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell014
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

theorem reflection_log_1_neg : (230150197 / 1000000000) ≤ -Real.log (1024 / 1289) ∧
    -Real.log (1024 / 1289) ≤ (115075099 / 500000000) := by
  have h := checkLog_sound (w := (265 / 2313)) (n := 12)
    (lo := (230150197 / 1000000000)) (hi := (115075099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1289 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1289 / 1024) = 1/(1024 / 1289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (230150197 / 1000000000) (115075099 / 500000000) (Real.log (1289 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1289 / 1024) = -Real.log (1024 / 1289) := by
    rw [show ((1289 / 1024) : ℝ) = ((1024 / 1289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (74867507 / 250000000) ≤ -Real.log (759 / 1024) ∧
    -Real.log (759 / 1024) ≤ (299470029 / 1000000000) := by
  have h := checkLog_sound (w := (265 / 1783)) (n := 12)
    (lo := (74867507 / 250000000)) (hi := (299470029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 759) = 1/(759 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-299470029 / 1000000000) (-74867507 / 250000000) (Real.log (759 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (229684611 / 1000000000) ≤ -Real.log (2560 / 3221) ∧
    -Real.log (2560 / 3221) ≤ (57421153 / 250000000) := by
  have h := checkLog_sound (w := (661 / 5781)) (n := 12)
    (lo := (229684611 / 1000000000)) (hi := (57421153 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3221 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3221 / 2560) = 1/(2560 / 3221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (229684611 / 1000000000) (57421153 / 250000000) (Real.log (3221 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3221 / 2560) = -Real.log (2560 / 3221) := by
    rw [show ((3221 / 2560) : ℝ) = ((2560 / 3221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (149339913 / 500000000) ≤ -Real.log (1899 / 2560) ∧
    -Real.log (1899 / 2560) ≤ (298679827 / 1000000000) := by
  have h := checkLog_sound (w := (661 / 4459)) (n := 12)
    (lo := (149339913 / 500000000)) (hi := (298679827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1899) = 1/(1899 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-298679827 / 1000000000) (-149339913 / 500000000) (Real.log (1899 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (168136421 / 1000000000) ≤ -Real.log (500000 / 591549) ∧
    -Real.log (500000 / 591549) ≤ (84068211 / 500000000) := by
  have h := checkLog_sound (w := (91549 / 1091549)) (n := 12)
    (lo := (168136421 / 1000000000)) (hi := (84068211 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591549 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591549 / 500000) = 1/(500000 / 591549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (168136421 / 1000000000) (84068211 / 500000000) (Real.log (591549 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (591549 / 500000) = -Real.log (500000 / 591549) := by
    rw [show ((591549 / 500000) : ℝ) = ((500000 / 591549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (101118071 / 500000000) ≤ -Real.log (408451 / 500000) ∧
    -Real.log (408451 / 500000) ≤ (202236143 / 1000000000) := by
  have h := checkLog_sound (w := (91549 / 908451)) (n := 12)
    (lo := (101118071 / 500000000)) (hi := (202236143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 408451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 408451) = 1/(408451 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-202236143 / 1000000000) (-101118071 / 500000000) (Real.log (408451 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (84245257 / 500000000) ≤ -Real.log (1000000 / 1183517) ∧
    -Real.log (1000000 / 1183517) ≤ (33698103 / 200000000) := by
  have h := checkLog_sound (w := (183517 / 2183517)) (n := 12)
    (lo := (84245257 / 500000000)) (hi := (33698103 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1183517 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1183517 / 1000000) = 1/(1000000 / 1183517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (84245257 / 500000000) (33698103 / 200000000) (Real.log (1183517 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1183517 / 1000000) = -Real.log (1000000 / 1183517) := by
    rw [show ((1183517 / 1000000) : ℝ) = ((1000000 / 1183517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (202749187 / 1000000000) ≤ -Real.log (816483 / 1000000) ∧
    -Real.log (816483 / 1000000) ≤ (50687297 / 250000000) := by
  have h := checkLog_sound (w := (183517 / 1816483)) (n := 12)
    (lo := (202749187 / 1000000000)) (hi := (50687297 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 816483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 816483) = 1/(816483 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-50687297 / 250000000) (-202749187 / 1000000000) (Real.log (816483 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (122822759 / 1000000000) ≤ -Real.log (250000 / 282671) ∧
    -Real.log (250000 / 282671) ≤ (3070569 / 25000000) := by
  have h := checkLog_sound (w := (32671 / 532671)) (n := 12)
    (lo := (122822759 / 1000000000)) (hi := (3070569 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((282671 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(282671 / 250000) = 1/(250000 / 282671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (122822759 / 1000000000) (3070569 / 25000000) (Real.log (282671 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (282671 / 250000) = -Real.log (250000 / 282671) := by
    rw [show ((282671 / 250000) : ℝ) = ((250000 / 282671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (140048583 / 1000000000) ≤ -Real.log (217329 / 250000) ∧
    -Real.log (217329 / 250000) ≤ (17506073 / 125000000) := by
  have h := checkLog_sound (w := (32671 / 467329)) (n := 12)
    (lo := (140048583 / 1000000000)) (hi := (17506073 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 217329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 217329) = 1/(217329 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-17506073 / 125000000) (-140048583 / 1000000000) (Real.log (217329 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (123092471 / 1000000000) ≤ -Real.log (1000000 / 1130989) ∧
    -Real.log (1000000 / 1130989) ≤ (15386559 / 125000000) := by
  have h := checkLog_sound (w := (130989 / 2130989)) (n := 12)
    (lo := (123092471 / 1000000000)) (hi := (15386559 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1130989 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1130989 / 1000000) = 1/(1000000 / 1130989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (123092471 / 1000000000) (15386559 / 125000000) (Real.log (1130989 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1130989 / 1000000) = -Real.log (1000000 / 1130989) := by
    rw [show ((1130989 / 1000000) : ℝ) = ((1000000 / 1130989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (28079899 / 200000000) ≤ -Real.log (869011 / 1000000) ∧
    -Real.log (869011 / 1000000) ≤ (17549937 / 125000000) := by
  have h := checkLog_sound (w := (130989 / 1869011)) (n := 12)
    (lo := (28079899 / 200000000)) (hi := (17549937 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 869011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 869011) = 1/(869011 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-17549937 / 125000000) (-28079899 / 200000000) (Real.log (869011 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (264182219 / 500000000) ≤ -Real.log (100000000000 / 169615587151) ∧
    -Real.log (100000000000 / 169615587151) ≤ (528364439 / 1000000000) := by
  have h := checkLog_sound (w := (69615587151 / 269615587151)) (n := 12)
    (lo := (264182219 / 500000000)) (hi := (528364439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169615587151 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169615587151 / 100000000000) = 1/(100000000000 / 169615587151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (264182219 / 500000000) (528364439 / 1000000000) (Real.log (169615587151 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (169615587151 / 100000000000) = -Real.log (100000000000 / 169615587151) := by
    rw [show ((169615587151 / 100000000000) : ℝ) = ((100000000000 / 169615587151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (21184809 / 40000000) ≤ -Real.log (250000000000 / 424571805007) ∧
    -Real.log (250000000000 / 424571805007) ≤ (264810113 / 500000000) := by
  have h := checkLog_sound (w := (174571805007 / 674571805007)) (n := 12)
    (lo := (21184809 / 40000000)) (hi := (264810113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((424571805007 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(424571805007 / 250000000000) = 1/(250000000000 / 424571805007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (21184809 / 40000000) (264810113 / 500000000) (Real.log (424571805007 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (424571805007 / 250000000000) = -Real.log (250000000000 / 424571805007) := by
    rw [show ((424571805007 / 250000000000) : ℝ) = ((250000000000 / 424571805007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (92593141 / 250000000) ≤ -Real.log (50000000000 / 72413704459) ∧
    -Real.log (50000000000 / 72413704459) ≤ (74074513 / 200000000) := by
  have h := checkLog_sound (w := (22413704459 / 122413704459)) (n := 12)
    (lo := (92593141 / 250000000)) (hi := (74074513 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((72413704459 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(72413704459 / 50000000000) = 1/(50000000000 / 72413704459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (92593141 / 250000000) (74074513 / 200000000) (Real.log (72413704459 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (72413704459 / 50000000000) = -Real.log (50000000000 / 72413704459) := by
    rw [show ((72413704459 / 50000000000) : ℝ) = ((50000000000 / 72413704459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (371239701 / 1000000000) ≤ -Real.log (500000000000 / 724765243123) ∧
    -Real.log (500000000000 / 724765243123) ≤ (185619851 / 500000000) := by
  have h := checkLog_sound (w := (224765243123 / 1224765243123)) (n := 12)
    (lo := (371239701 / 1000000000)) (hi := (185619851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((724765243123 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(724765243123 / 500000000000) = 1/(500000000000 / 724765243123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (371239701 / 1000000000) (185619851 / 500000000) (Real.log (724765243123 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (724765243123 / 500000000000) = -Real.log (500000000000 / 724765243123) := by
    rw [show ((724765243123 / 500000000000) : ℝ) = ((500000000000 / 724765243123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (131435671 / 500000000) ≤ -Real.log (500000000000 / 650329684487) ∧
    -Real.log (500000000000 / 650329684487) ≤ (262871343 / 1000000000) := by
  have h := checkLog_sound (w := (150329684487 / 1150329684487)) (n := 12)
    (lo := (131435671 / 500000000)) (hi := (262871343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((650329684487 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(650329684487 / 500000000000) = 1/(500000000000 / 650329684487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (131435671 / 500000000) (262871343 / 1000000000) (Real.log (650329684487 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (650329684487 / 500000000000) = -Real.log (500000000000 / 650329684487) := by
    rw [show ((650329684487 / 500000000000) : ℝ) = ((500000000000 / 650329684487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (131745983 / 500000000) ≤ -Real.log (250000000000 / 325366709973) ∧
    -Real.log (250000000000 / 325366709973) ≤ (263491967 / 1000000000) := by
  have h := checkLog_sound (w := (75366709973 / 575366709973)) (n := 12)
    (lo := (131745983 / 500000000)) (hi := (263491967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((325366709973 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(325366709973 / 250000000000) = 1/(250000000000 / 325366709973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (131745983 / 500000000) (263491967 / 1000000000) (Real.log (325366709973 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (325366709973 / 250000000000) = -Real.log (250000000000 / 325366709973) := by
    rw [show ((325366709973 / 250000000000) : ℝ) = ((250000000000 / 325366709973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1081689 / 62500000) ≤ -Real.log (982841881879 / 1000000000000) ∧
    -Real.log (982841881879 / 1000000000000) ≤ (692281 / 40000000) := by
  have h := checkLog_sound (w := (17158118121 / 1982841881879)) (n := 12)
    (lo := (1081689 / 62500000)) (hi := (692281 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 982841881879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 982841881879) = 1/(982841881879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-692281 / 40000000) (-1081689 / 62500000) (Real.log (982841881879 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (538307 / 31250000) ≤ -Real.log (61432605759 / 62500000000) ∧
    -Real.log (61432605759 / 62500000000) ≤ (689033 / 40000000) := by
  have h := checkLog_sound (w := (1067394241 / 123932605759)) (n := 12)
    (lo := (538307 / 31250000)) (hi := (689033 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61432605759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61432605759) = 1/(61432605759 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-689033 / 40000000) (-538307 / 31250000) (Real.log (61432605759 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell014
