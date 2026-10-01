import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell043
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

theorem reflection_log_1_neg : (15222421 / 62500000) ≤ -Real.log (1280 / 1633) ∧
    -Real.log (1280 / 1633) ≤ (243558737 / 1000000000) := by
  have h := checkLog_sound (w := (353 / 2913)) (n := 12)
    (lo := (15222421 / 62500000)) (hi := (243558737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1633 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1633 / 1280) = 1/(1280 / 1633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (15222421 / 62500000) (243558737 / 1000000000) (Real.log (1633 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1633 / 1280) = -Real.log (1280 / 1633) := by
    rw [show ((1633 / 1280) : ℝ) = ((1280 / 1633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (322661791 / 1000000000) ≤ -Real.log (927 / 1280) ∧
    -Real.log (927 / 1280) ≤ (10083181 / 31250000) := by
  have h := checkLog_sound (w := (353 / 2207)) (n := 12)
    (lo := (322661791 / 1000000000)) (hi := (10083181 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 927) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 927) = 1/(927 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-10083181 / 31250000) (-322661791 / 1000000000) (Real.log (927 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (243099353 / 1000000000) ≤ -Real.log (5120 / 6529) ∧
    -Real.log (5120 / 6529) ≤ (121549677 / 500000000) := by
  have h := checkLog_sound (w := (1409 / 11649)) (n := 12)
    (lo := (243099353 / 1000000000)) (hi := (121549677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6529 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6529 / 5120) = 1/(5120 / 6529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (243099353 / 1000000000) (121549677 / 500000000) (Real.log (6529 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6529 / 5120) = -Real.log (5120 / 6529) := by
    rw [show ((6529 / 5120) : ℝ) = ((5120 / 6529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2514477 / 7812500) ≤ -Real.log (3711 / 5120) ∧
    -Real.log (3711 / 5120) ≤ (321853057 / 1000000000) := by
  have h := checkLog_sound (w := (1409 / 8831)) (n := 12)
    (lo := (2514477 / 7812500)) (hi := (321853057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3711) = 1/(3711 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-321853057 / 1000000000) (-2514477 / 7812500) (Real.log (3711 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (22291911 / 125000000) ≤ -Real.log (500000 / 597613) ∧
    -Real.log (500000 / 597613) ≤ (178335289 / 1000000000) := by
  have h := checkLog_sound (w := (97613 / 1097613)) (n := 12)
    (lo := (22291911 / 125000000)) (hi := (178335289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597613 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597613 / 500000) = 1/(500000 / 597613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (22291911 / 125000000) (178335289 / 1000000000) (Real.log (597613 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (597613 / 500000) = -Real.log (500000 / 597613) := by
    rw [show ((597613 / 500000) : ℝ) = ((500000 / 597613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (108596893 / 500000000) ≤ -Real.log (402387 / 500000) ∧
    -Real.log (402387 / 500000) ≤ (217193787 / 1000000000) := by
  have h := checkLog_sound (w := (97613 / 902387)) (n := 12)
    (lo := (108596893 / 500000000)) (hi := (217193787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 402387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 402387) = 1/(402387 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-217193787 / 1000000000) (-108596893 / 500000000) (Real.log (402387 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (1429493 / 8000000) ≤ -Real.log (500000 / 597823) ∧
    -Real.log (500000 / 597823) ≤ (89343313 / 500000000) := by
  have h := checkLog_sound (w := (97823 / 1097823)) (n := 12)
    (lo := (1429493 / 8000000)) (hi := (89343313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597823 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597823 / 500000) = 1/(500000 / 597823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (1429493 / 8000000) (89343313 / 500000000) (Real.log (597823 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (597823 / 500000) = -Real.log (500000 / 597823) := by
    rw [show ((597823 / 500000) : ℝ) = ((500000 / 597823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (6803619 / 31250000) ≤ -Real.log (402177 / 500000) ∧
    -Real.log (402177 / 500000) ≤ (217715809 / 1000000000) := by
  have h := checkLog_sound (w := (97823 / 902177)) (n := 12)
    (lo := (6803619 / 31250000)) (hi := (217715809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 402177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 402177) = 1/(402177 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-217715809 / 1000000000) (-6803619 / 31250000) (Real.log (402177 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (130606243 / 1000000000) ≤ -Real.log (1000000 / 1139519) ∧
    -Real.log (1000000 / 1139519) ≤ (32651561 / 250000000) := by
  have h := checkLog_sound (w := (139519 / 2139519)) (n := 12)
    (lo := (130606243 / 1000000000)) (hi := (32651561 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1139519 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1139519 / 1000000) = 1/(1000000 / 1139519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (130606243 / 1000000000) (32651561 / 250000000) (Real.log (1139519 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1139519 / 1000000) = -Real.log (1000000 / 1139519) := by
    rw [show ((1139519 / 1000000) : ℝ) = ((1000000 / 1139519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (150263743 / 1000000000) ≤ -Real.log (860481 / 1000000) ∧
    -Real.log (860481 / 1000000) ≤ (2347871 / 15625000) := by
  have h := checkLog_sound (w := (139519 / 1860481)) (n := 12)
    (lo := (150263743 / 1000000000)) (hi := (2347871 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 860481) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 860481) = 1/(860481 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2347871 / 15625000) (-150263743 / 1000000000) (Real.log (860481 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (130875619 / 1000000000) ≤ -Real.log (500000 / 569913) ∧
    -Real.log (500000 / 569913) ≤ (6543781 / 50000000) := by
  have h := checkLog_sound (w := (69913 / 1069913)) (n := 12)
    (lo := (130875619 / 1000000000)) (hi := (6543781 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((569913 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(569913 / 500000) = 1/(500000 / 569913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (130875619 / 1000000000) (6543781 / 50000000) (Real.log (569913 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (569913 / 500000) = -Real.log (500000 / 569913) := by
    rw [show ((569913 / 500000) : ℝ) = ((500000 / 569913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (18827573 / 125000000) ≤ -Real.log (430087 / 500000) ∧
    -Real.log (430087 / 500000) ≤ (30124117 / 200000000) := by
  have h := checkLog_sound (w := (69913 / 930087)) (n := 12)
    (lo := (18827573 / 125000000)) (hi := (30124117 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 430087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 430087) = 1/(430087 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-30124117 / 200000000) (-18827573 / 125000000) (Real.log (430087 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (56495241 / 100000000) ≤ -Real.log (500000000000 / 879682026407) ∧
    -Real.log (500000000000 / 879682026407) ≤ (564952411 / 1000000000) := by
  have h := checkLog_sound (w := (379682026407 / 1379682026407)) (n := 12)
    (lo := (56495241 / 100000000)) (hi := (564952411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((879682026407 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(879682026407 / 500000000000) = 1/(500000000000 / 879682026407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (56495241 / 100000000) (564952411 / 1000000000) (Real.log (879682026407 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (879682026407 / 500000000000) = -Real.log (500000000000 / 879682026407) := by
    rw [show ((879682026407 / 500000000000) : ℝ) = ((500000000000 / 879682026407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (566220527 / 1000000000) ≤ -Real.log (500000000000 / 880798274003) ∧
    -Real.log (500000000000 / 880798274003) ≤ (35388783 / 62500000) := by
  have h := checkLog_sound (w := (380798274003 / 1380798274003)) (n := 12)
    (lo := (566220527 / 1000000000)) (hi := (35388783 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((880798274003 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(880798274003 / 500000000000) = 1/(500000000000 / 880798274003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (566220527 / 1000000000) (35388783 / 62500000) (Real.log (880798274003 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (880798274003 / 500000000000) = -Real.log (500000000000 / 880798274003) := by
    rw [show ((880798274003 / 500000000000) : ℝ) = ((500000000000 / 880798274003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (15821163 / 40000000) ≤ -Real.log (500000000000 / 742584874759) ∧
    -Real.log (500000000000 / 742584874759) ≤ (98882269 / 250000000) := by
  have h := checkLog_sound (w := (242584874759 / 1242584874759)) (n := 12)
    (lo := (15821163 / 40000000)) (hi := (98882269 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742584874759 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(742584874759 / 500000000000) = 1/(500000000000 / 742584874759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (15821163 / 40000000) (98882269 / 250000000) (Real.log (742584874759 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (742584874759 / 500000000000) = -Real.log (500000000000 / 742584874759) := by
    rw [show ((742584874759 / 500000000000) : ℝ) = ((500000000000 / 742584874759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (396402433 / 1000000000) ≤ -Real.log (100000000000 / 148646740117) ∧
    -Real.log (100000000000 / 148646740117) ≤ (198201217 / 500000000) := by
  have h := checkLog_sound (w := (48646740117 / 248646740117)) (n := 12)
    (lo := (396402433 / 1000000000)) (hi := (198201217 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148646740117 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148646740117 / 100000000000) = 1/(100000000000 / 148646740117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (396402433 / 1000000000) (198201217 / 500000000) (Real.log (148646740117 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (148646740117 / 100000000000) = -Real.log (100000000000 / 148646740117) := by
    rw [show ((148646740117 / 100000000000) : ℝ) = ((100000000000 / 148646740117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (280869987 / 1000000000) ≤ -Real.log (62500000000 / 82767588709) ∧
    -Real.log (62500000000 / 82767588709) ≤ (70217497 / 250000000) := by
  have h := checkLog_sound (w := (20267588709 / 145267588709)) (n := 12)
    (lo := (280869987 / 1000000000)) (hi := (70217497 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82767588709 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82767588709 / 62500000000) = 1/(62500000000 / 82767588709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (280869987 / 1000000000) (70217497 / 250000000) (Real.log (82767588709 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (82767588709 / 62500000000) = -Real.log (62500000000 / 82767588709) := by
    rw [show ((82767588709 / 62500000000) : ℝ) = ((62500000000 / 82767588709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (281496203 / 1000000000) ≤ -Real.log (500000000000 / 662555482961) ∧
    -Real.log (500000000000 / 662555482961) ≤ (70374051 / 250000000) := by
  have h := checkLog_sound (w := (162555482961 / 1162555482961)) (n := 12)
    (lo := (281496203 / 1000000000)) (hi := (70374051 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((662555482961 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(662555482961 / 500000000000) = 1/(500000000000 / 662555482961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (281496203 / 1000000000) (70374051 / 250000000) (Real.log (662555482961 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (662555482961 / 500000000000) = -Real.log (500000000000 / 662555482961) := by
    rw [show ((662555482961 / 500000000000) : ℝ) = ((500000000000 / 662555482961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3948993 / 200000000) ≤ -Real.log (245112172431 / 250000000000) ∧
    -Real.log (245112172431 / 250000000000) ≤ (9872483 / 500000000) := by
  have h := checkLog_sound (w := (4887827569 / 495112172431)) (n := 12)
    (lo := (3948993 / 200000000)) (hi := (9872483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245112172431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245112172431) = 1/(245112172431 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-9872483 / 500000000) (-3948993 / 200000000) (Real.log (245112172431 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (7863 / 400000) ≤ -Real.log (980534448639 / 1000000000000) ∧
    -Real.log (980534448639 / 1000000000000) ≤ (19657501 / 1000000000) := by
  have h := checkLog_sound (w := (19465551361 / 1980534448639)) (n := 12)
    (lo := (7863 / 400000)) (hi := (19657501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 980534448639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 980534448639) = 1/(980534448639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-19657501 / 1000000000) (-7863 / 400000) (Real.log (980534448639 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell043
