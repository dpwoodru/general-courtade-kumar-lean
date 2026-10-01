import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0443
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

theorem reflection_log_1_neg : (189861419 / 1000000000) ≤ -Real.log (10240 / 12381) ∧
    -Real.log (10240 / 12381) ≤ (9493071 / 50000000) := by
  have h := checkLog_sound (w := (2141 / 22621)) (n := 12)
    (lo := (189861419 / 1000000000)) (hi := (9493071 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12381 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12381 / 10240) = 1/(10240 / 12381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (189861419 / 1000000000) (9493071 / 50000000) (Real.log (12381 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12381 / 10240) = -Real.log (10240 / 12381) := by
    rw [show ((12381 / 10240) : ℝ) = ((10240 / 12381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (117280511 / 500000000) ≤ -Real.log (8099 / 10240) ∧
    -Real.log (8099 / 10240) ≤ (234561023 / 1000000000) := by
  have h := checkLog_sound (w := (2141 / 18339)) (n := 12)
    (lo := (117280511 / 500000000)) (hi := (234561023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8099) = 1/(8099 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-234561023 / 1000000000) (-117280511 / 500000000) (Real.log (8099 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (189619083 / 1000000000) ≤ -Real.log (5120 / 6189) ∧
    -Real.log (5120 / 6189) ≤ (47404771 / 250000000) := by
  have h := checkLog_sound (w := (1069 / 11309)) (n := 12)
    (lo := (189619083 / 1000000000)) (hi := (47404771 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6189 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6189 / 5120) = 1/(5120 / 6189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (189619083 / 1000000000) (47404771 / 250000000) (Real.log (6189 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6189 / 5120) = -Real.log (5120 / 6189) := by
    rw [show ((6189 / 5120) : ℝ) = ((5120 / 6189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (117095337 / 500000000) ≤ -Real.log (4051 / 5120) ∧
    -Real.log (4051 / 5120) ≤ (9367627 / 40000000) := by
  have h := checkLog_sound (w := (1069 / 9171)) (n := 12)
    (lo := (117095337 / 500000000)) (hi := (9367627 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4051) = 1/(4051 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-9367627 / 40000000) (-117095337 / 500000000) (Real.log (4051 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (349363121 / 1000000000) ≤ -Real.log (5120 / 7261) ∧
    -Real.log (5120 / 7261) ≤ (174681561 / 500000000) := by
  have h := checkLog_sound (w := (2141 / 12381)) (n := 12)
    (lo := (349363121 / 1000000000)) (hi := (174681561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7261 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7261 / 5120) = 1/(5120 / 7261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (349363121 / 1000000000) (174681561 / 500000000) (Real.log (7261 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7261 / 5120) = -Real.log (5120 / 7261) := by
    rw [show ((7261 / 5120) : ℝ) = ((5120 / 7261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (108313353 / 200000000) ≤ -Real.log (2979 / 5120) ∧
    -Real.log (2979 / 5120) ≤ (270783383 / 500000000) := by
  have h := checkLog_sound (w := (2141 / 8099)) (n := 12)
    (lo := (108313353 / 200000000)) (hi := (270783383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2979) = 1/(2979 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-270783383 / 500000000) (-108313353 / 200000000) (Real.log (2979 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (348949869 / 1000000000) ≤ -Real.log (2560 / 3629) ∧
    -Real.log (2560 / 3629) ≤ (34894987 / 100000000) := by
  have h := checkLog_sound (w := (1069 / 6189)) (n := 12)
    (lo := (348949869 / 1000000000)) (hi := (34894987 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3629 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3629 / 2560) = 1/(2560 / 3629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (348949869 / 1000000000) (34894987 / 100000000) (Real.log (3629 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3629 / 2560) = -Real.log (2560 / 3629) := by
    rw [show ((3629 / 2560) : ℝ) = ((2560 / 3629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (270280111 / 500000000) ≤ -Real.log (1491 / 2560) ∧
    -Real.log (1491 / 2560) ≤ (540560223 / 1000000000) := by
  have h := checkLog_sound (w := (1069 / 4051)) (n := 12)
    (lo := (270280111 / 500000000)) (hi := (540560223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1491) = 1/(1491 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-540560223 / 1000000000) (-270280111 / 500000000) (Real.log (1491 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (65126789 / 250000000) ≤ -Real.log (250000 / 324397) ∧
    -Real.log (250000 / 324397) ≤ (260507157 / 1000000000) := by
  have h := checkLog_sound (w := (74397 / 574397)) (n := 12)
    (lo := (65126789 / 250000000)) (hi := (260507157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((324397 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(324397 / 250000) = 1/(250000 / 324397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (65126789 / 250000000) (260507157 / 1000000000) (Real.log (324397 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (324397 / 250000) = -Real.log (250000 / 324397) := by
    rw [show ((324397 / 250000) : ℝ) = ((250000 / 324397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (22077197 / 62500000) ≤ -Real.log (175603 / 250000) ∧
    -Real.log (175603 / 250000) ≤ (353235153 / 1000000000) := by
  have h := checkLog_sound (w := (74397 / 425603)) (n := 12)
    (lo := (22077197 / 62500000)) (hi := (353235153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 175603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 175603) = 1/(175603 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-353235153 / 1000000000) (-22077197 / 62500000) (Real.log (175603 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (65208851 / 250000000) ≤ -Real.log (500000 / 649007) ∧
    -Real.log (500000 / 649007) ≤ (52167081 / 200000000) := by
  have h := checkLog_sound (w := (149007 / 1149007)) (n := 12)
    (lo := (65208851 / 250000000)) (hi := (52167081 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((649007 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(649007 / 500000) = 1/(500000 / 649007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (65208851 / 250000000) (52167081 / 200000000) (Real.log (649007 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (649007 / 500000) = -Real.log (500000 / 649007) := by
    rw [show ((649007 / 500000) : ℝ) = ((500000 / 649007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (176920909 / 500000000) ≤ -Real.log (350993 / 500000) ∧
    -Real.log (350993 / 500000) ≤ (353841819 / 1000000000) := by
  have h := checkLog_sound (w := (149007 / 850993)) (n := 12)
    (lo := (176920909 / 500000000)) (hi := (353841819 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 350993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 350993) = 1/(350993 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-353841819 / 1000000000) (-176920909 / 500000000) (Real.log (350993 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (195333203 / 1000000000) ≤ -Real.log (250000 / 303929) ∧
    -Real.log (250000 / 303929) ≤ (48833301 / 250000000) := by
  have h := checkLog_sound (w := (53929 / 553929)) (n := 12)
    (lo := (195333203 / 1000000000)) (hi := (48833301 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303929 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303929 / 250000) = 1/(250000 / 303929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (195333203 / 1000000000) (48833301 / 250000000) (Real.log (303929 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (303929 / 250000) = -Real.log (250000 / 303929) := by
    rw [show ((303929 / 250000) : ℝ) = ((250000 / 303929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (242984079 / 1000000000) ≤ -Real.log (196071 / 250000) ∧
    -Real.log (196071 / 250000) ≤ (3037301 / 12500000) := by
  have h := checkLog_sound (w := (53929 / 446071)) (n := 12)
    (lo := (242984079 / 1000000000)) (hi := (3037301 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 196071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 196071) = 1/(196071 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3037301 / 12500000) (-242984079 / 1000000000) (Real.log (196071 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (195599677 / 1000000000) ≤ -Real.log (25000 / 30401) ∧
    -Real.log (25000 / 30401) ≤ (97799839 / 500000000) := by
  have h := checkLog_sound (w := (5401 / 55401)) (n := 12)
    (lo := (195599677 / 1000000000)) (hi := (97799839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30401 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30401 / 25000) = 1/(25000 / 30401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (195599677 / 1000000000) (97799839 / 500000000) (Real.log (30401 / 25000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (30401 / 25000) = -Real.log (25000 / 30401) := by
    rw [show ((30401 / 25000) : ℝ) = ((25000 / 30401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1521233 / 6250000) ≤ -Real.log (19599 / 25000) ∧
    -Real.log (19599 / 25000) ≤ (243397281 / 1000000000) := by
  have h := checkLog_sound (w := (5401 / 44599)) (n := 12)
    (lo := (1521233 / 6250000)) (hi := (243397281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 19599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 19599) = 1/(19599 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-243397281 / 1000000000) (-1521233 / 6250000) (Real.log (19599 / 25000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (613742309 / 1000000000) ≤ -Real.log (500000000000 / 923665882701) ∧
    -Real.log (500000000000 / 923665882701) ≤ (61374231 / 100000000) := by
  have h := checkLog_sound (w := (423665882701 / 1423665882701)) (n := 12)
    (lo := (613742309 / 1000000000)) (hi := (61374231 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((923665882701 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(923665882701 / 500000000000) = 1/(500000000000 / 923665882701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (613742309 / 1000000000) (61374231 / 100000000) (Real.log (923665882701 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (923665882701 / 500000000000) = -Real.log (500000000000 / 923665882701) := by
    rw [show ((923665882701 / 500000000000) : ℝ) = ((500000000000 / 923665882701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (307338611 / 500000000) ≤ -Real.log (500000000000 / 924529833929) ∧
    -Real.log (500000000000 / 924529833929) ≤ (614677223 / 1000000000) := by
  have h := checkLog_sound (w := (424529833929 / 1424529833929)) (n := 12)
    (lo := (307338611 / 500000000)) (hi := (614677223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((924529833929 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(924529833929 / 500000000000) = 1/(500000000000 / 924529833929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (307338611 / 500000000) (614677223 / 1000000000) (Real.log (924529833929 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (924529833929 / 500000000000) = -Real.log (500000000000 / 924529833929) := by
    rw [show ((924529833929 / 500000000000) : ℝ) = ((500000000000 / 924529833929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (219158641 / 500000000) ≤ -Real.log (500000000000 / 775048324331) ∧
    -Real.log (500000000000 / 775048324331) ≤ (438317283 / 1000000000) := by
  have h := checkLog_sound (w := (275048324331 / 1275048324331)) (n := 12)
    (lo := (219158641 / 500000000)) (hi := (438317283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((775048324331 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(775048324331 / 500000000000) = 1/(500000000000 / 775048324331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (219158641 / 500000000) (438317283 / 1000000000) (Real.log (775048324331 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (775048324331 / 500000000000) = -Real.log (500000000000 / 775048324331) := by
    rw [show ((775048324331 / 500000000000) : ℝ) = ((500000000000 / 775048324331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (219498479 / 500000000) ≤ -Real.log (250000000000 / 387787642227) ∧
    -Real.log (250000000000 / 387787642227) ≤ (438996959 / 1000000000) := by
  have h := checkLog_sound (w := (137787642227 / 637787642227)) (n := 12)
    (lo := (219498479 / 500000000)) (hi := (438996959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387787642227 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(387787642227 / 250000000000) = 1/(250000000000 / 387787642227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (219498479 / 500000000) (438996959 / 1000000000) (Real.log (387787642227 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (387787642227 / 250000000000) = -Real.log (250000000000 / 387787642227) := by
    rw [show ((387787642227 / 250000000000) : ℝ) = ((250000000000 / 387787642227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0443
