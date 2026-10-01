import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0449
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

theorem reflection_log_1_neg : (188406521 / 1000000000) ≤ -Real.log (10240 / 12363) ∧
    -Real.log (10240 / 12363) ≤ (94203261 / 500000000) := by
  have h := checkLog_sound (w := (2123 / 22603)) (n := 12)
    (lo := (188406521 / 1000000000)) (hi := (94203261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12363 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12363 / 10240) = 1/(10240 / 12363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (188406521 / 1000000000) (94203261 / 500000000) (Real.log (12363 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12363 / 10240) = -Real.log (10240 / 12363) := by
    rw [show ((12363 / 10240) : ℝ) = ((10240 / 12363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (232340991 / 1000000000) ≤ -Real.log (8117 / 10240) ∧
    -Real.log (8117 / 10240) ≤ (453791 / 1953125) := by
  have h := checkLog_sound (w := (2123 / 18357)) (n := 12)
    (lo := (232340991 / 1000000000)) (hi := (453791 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8117) = 1/(8117 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-453791 / 1953125) (-232340991 / 1000000000) (Real.log (8117 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (23520479 / 125000000) ≤ -Real.log (256 / 309) ∧
    -Real.log (256 / 309) ≤ (188163833 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 565)) (n := 12)
    (lo := (23520479 / 125000000)) (hi := (188163833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((309 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(309 / 256) = 1/(256 / 309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (23520479 / 125000000) (188163833 / 1000000000) (Real.log (309 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (309 / 256) = -Real.log (256 / 309) := by
    rw [show ((309 / 256) : ℝ) = ((256 / 309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (46394293 / 200000000) ≤ -Real.log (203 / 256) ∧
    -Real.log (203 / 256) ≤ (115985733 / 500000000) := by
  have h := checkLog_sound (w := (53 / 459)) (n := 12)
    (lo := (46394293 / 200000000)) (hi := (115985733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 203) = 1/(203 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-115985733 / 500000000) (-46394293 / 200000000) (Real.log (203 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (173440523 / 500000000) ≤ -Real.log (5120 / 7243) ∧
    -Real.log (5120 / 7243) ≤ (346881047 / 1000000000) := by
  have h := checkLog_sound (w := (2123 / 12363)) (n := 12)
    (lo := (173440523 / 500000000)) (hi := (346881047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7243 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7243 / 5120) = 1/(5120 / 7243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (173440523 / 500000000) (346881047 / 1000000000) (Real.log (7243 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7243 / 5120) = -Real.log (5120 / 7243) := by
    rw [show ((7243 / 5120) : ℝ) = ((5120 / 7243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (10710853 / 20000000) ≤ -Real.log (2997 / 5120) ∧
    -Real.log (2997 / 5120) ≤ (535542651 / 1000000000) := by
  have h := checkLog_sound (w := (2123 / 8117)) (n := 12)
    (lo := (10710853 / 20000000)) (hi := (535542651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2997) = 1/(2997 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-535542651 / 1000000000) (-10710853 / 20000000) (Real.log (2997 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (346466767 / 1000000000) ≤ -Real.log (128 / 181) ∧
    -Real.log (128 / 181) ≤ (21654173 / 62500000) := by
  have h := checkLog_sound (w := (53 / 309)) (n := 12)
    (lo := (346466767 / 1000000000)) (hi := (21654173 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181 / 128) = 1/(128 / 181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (346466767 / 1000000000) (21654173 / 62500000) (Real.log (181 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (181 / 128) = -Real.log (128 / 181) := by
    rw [show ((181 / 128) : ℝ) = ((128 / 181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (10690843 / 20000000) ≤ -Real.log (75 / 128) ∧
    -Real.log (75 / 128) ≤ (534542151 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 203)) (n := 12)
    (lo := (10690843 / 20000000)) (hi := (534542151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 75) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 75) = 1/(75 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-534542151 / 1000000000) (-10690843 / 20000000) (Real.log (75 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (129271177 / 500000000) ≤ -Real.log (1000000 / 1295041) ∧
    -Real.log (1000000 / 1295041) ≤ (51708471 / 200000000) := by
  have h := checkLog_sound (w := (295041 / 2295041)) (n := 12)
    (lo := (129271177 / 500000000)) (hi := (51708471 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1295041 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1295041 / 1000000) = 1/(1000000 / 1295041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (129271177 / 500000000) (51708471 / 200000000) (Real.log (1295041 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1295041 / 1000000) = -Real.log (1000000 / 1295041) := by
    rw [show ((1295041 / 1000000) : ℝ) = ((1000000 / 1295041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (349615633 / 1000000000) ≤ -Real.log (704959 / 1000000) ∧
    -Real.log (704959 / 1000000) ≤ (174807817 / 500000000) := by
  have h := checkLog_sound (w := (295041 / 1704959)) (n := 12)
    (lo := (349615633 / 1000000000)) (hi := (174807817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 704959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 704959) = 1/(704959 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-174807817 / 500000000) (-349615633 / 1000000000) (Real.log (704959 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (258871247 / 1000000000) ≤ -Real.log (1000000 / 1295467) ∧
    -Real.log (1000000 / 1295467) ≤ (16179453 / 62500000) := by
  have h := checkLog_sound (w := (295467 / 2295467)) (n := 12)
    (lo := (258871247 / 1000000000)) (hi := (16179453 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1295467 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1295467 / 1000000) = 1/(1000000 / 1295467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (258871247 / 1000000000) (16179453 / 62500000) (Real.log (1295467 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1295467 / 1000000) = -Real.log (1000000 / 1295467) := by
    rw [show ((1295467 / 1000000) : ℝ) = ((1000000 / 1295467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (350220107 / 1000000000) ≤ -Real.log (704533 / 1000000) ∧
    -Real.log (704533 / 1000000) ≤ (87555027 / 250000000) := by
  have h := checkLog_sound (w := (295467 / 1704533)) (n := 12)
    (lo := (350220107 / 1000000000)) (hi := (87555027 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 704533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 704533) = 1/(704533 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-87555027 / 250000000) (-350220107 / 1000000000) (Real.log (704533 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (193737809 / 1000000000) ≤ -Real.log (500000 / 606889) ∧
    -Real.log (500000 / 606889) ≤ (19373781 / 100000000) := by
  have h := checkLog_sound (w := (106889 / 1106889)) (n := 12)
    (lo := (193737809 / 1000000000)) (hi := (19373781 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((606889 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(606889 / 500000) = 1/(500000 / 606889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (193737809 / 1000000000) (19373781 / 100000000) (Real.log (606889 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (606889 / 500000) = -Real.log (500000 / 606889) := by
    rw [show ((606889 / 500000) : ℝ) = ((500000 / 606889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (240516083 / 1000000000) ≤ -Real.log (393111 / 500000) ∧
    -Real.log (393111 / 500000) ≤ (60129021 / 250000000) := by
  have h := checkLog_sound (w := (106889 / 893111)) (n := 12)
    (lo := (240516083 / 1000000000)) (hi := (60129021 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 393111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 393111) = 1/(393111 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-60129021 / 250000000) (-240516083 / 1000000000) (Real.log (393111 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (48501177 / 250000000) ≤ -Real.log (500000 / 607051) ∧
    -Real.log (500000 / 607051) ≤ (194004709 / 1000000000) := by
  have h := checkLog_sound (w := (107051 / 1107051)) (n := 12)
    (lo := (48501177 / 250000000)) (hi := (194004709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607051 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607051 / 500000) = 1/(500000 / 607051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (48501177 / 250000000) (194004709 / 1000000000) (Real.log (607051 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (607051 / 500000) = -Real.log (500000 / 607051) := by
    rw [show ((607051 / 500000) : ℝ) = ((500000 / 607051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (48185653 / 200000000) ≤ -Real.log (392949 / 500000) ∧
    -Real.log (392949 / 500000) ≤ (120464133 / 500000000) := by
  have h := checkLog_sound (w := (107051 / 892949)) (n := 12)
    (lo := (48185653 / 200000000)) (hi := (120464133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 392949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 392949) = 1/(392949 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-120464133 / 500000000) (-48185653 / 200000000) (Real.log (392949 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (152039497 / 250000000) ≤ -Real.log (50000000000 / 91852221193) ∧
    -Real.log (50000000000 / 91852221193) ≤ (608157989 / 1000000000) := by
  have h := checkLog_sound (w := (41852221193 / 141852221193)) (n := 12)
    (lo := (152039497 / 250000000)) (hi := (608157989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91852221193 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(91852221193 / 50000000000) = 1/(50000000000 / 91852221193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (152039497 / 250000000) (608157989 / 1000000000) (Real.log (91852221193 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (91852221193 / 50000000000) = -Real.log (50000000000 / 91852221193) := by
    rw [show ((91852221193 / 50000000000) : ℝ) = ((50000000000 / 91852221193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (304545677 / 500000000) ≤ -Real.log (125000000000 / 229844982421) ∧
    -Real.log (125000000000 / 229844982421) ≤ (121818271 / 200000000) := by
  have h := checkLog_sound (w := (104844982421 / 354844982421)) (n := 12)
    (lo := (304545677 / 500000000)) (hi := (121818271 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229844982421 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(229844982421 / 125000000000) = 1/(125000000000 / 229844982421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (304545677 / 500000000) (121818271 / 200000000) (Real.log (229844982421 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (229844982421 / 125000000000) = -Real.log (125000000000 / 229844982421) := by
    rw [show ((229844982421 / 125000000000) : ℝ) = ((125000000000 / 229844982421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (434253893 / 1000000000) ≤ -Real.log (500000000000 / 771905390589) ∧
    -Real.log (500000000000 / 771905390589) ≤ (217126947 / 500000000) := by
  have h := checkLog_sound (w := (271905390589 / 1271905390589)) (n := 12)
    (lo := (434253893 / 1000000000)) (hi := (217126947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((771905390589 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(771905390589 / 500000000000) = 1/(500000000000 / 771905390589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (434253893 / 1000000000) (217126947 / 500000000) (Real.log (771905390589 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (771905390589 / 500000000000) = -Real.log (500000000000 / 771905390589) := by
    rw [show ((771905390589 / 500000000000) : ℝ) = ((500000000000 / 771905390589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (217466487 / 500000000) ≤ -Real.log (125000000000 / 193107438879) ∧
    -Real.log (125000000000 / 193107438879) ≤ (17397319 / 40000000) := by
  have h := checkLog_sound (w := (68107438879 / 318107438879)) (n := 12)
    (lo := (217466487 / 500000000)) (hi := (17397319 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((193107438879 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(193107438879 / 125000000000) = 1/(125000000000 / 193107438879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (217466487 / 500000000) (17397319 / 40000000) (Real.log (193107438879 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (193107438879 / 125000000000) = -Real.log (125000000000 / 193107438879) := by
    rw [show ((193107438879 / 125000000000) : ℝ) = ((125000000000 / 193107438879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0449
