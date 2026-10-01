import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell036
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

theorem reflection_log_1_neg : (48067723 / 200000000) ≤ -Real.log (5120 / 6511) ∧
    -Real.log (5120 / 6511) ≤ (30042327 / 125000000) := by
  have h := checkLog_sound (w := (1391 / 11631)) (n := 12)
    (lo := (48067723 / 200000000)) (hi := (30042327 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6511 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6511 / 5120) = 1/(5120 / 6511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (48067723 / 200000000) (30042327 / 125000000) (Real.log (6511 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6511 / 5120) = -Real.log (5120 / 6511) := by
    rw [show ((6511 / 5120) : ℝ) = ((5120 / 6511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (317014337 / 1000000000) ≤ -Real.log (3729 / 5120) ∧
    -Real.log (3729 / 5120) ≤ (158507169 / 500000000) := by
  have h := checkLog_sound (w := (1391 / 8849)) (n := 12)
    (lo := (317014337 / 1000000000)) (hi := (158507169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3729) = 1/(3729 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-158507169 / 500000000) (-317014337 / 1000000000) (Real.log (3729 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (959511 / 4000000) ≤ -Real.log (1280 / 1627) ∧
    -Real.log (1280 / 1627) ≤ (239877751 / 1000000000) := by
  have h := checkLog_sound (w := (347 / 2907)) (n := 12)
    (lo := (959511 / 4000000)) (hi := (239877751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1627 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1627 / 1280) = 1/(1280 / 1627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (959511 / 4000000) (239877751 / 1000000000) (Real.log (1627 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1627 / 1280) = -Real.log (1280 / 1627) := by
    rw [show ((1627 / 1280) : ℝ) = ((1280 / 1627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (79052539 / 250000000) ≤ -Real.log (933 / 1280) ∧
    -Real.log (933 / 1280) ≤ (316210157 / 1000000000) := by
  have h := checkLog_sound (w := (347 / 2213)) (n := 12)
    (lo := (79052539 / 250000000)) (hi := (316210157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 933) = 1/(933 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-316210157 / 1000000000) (-79052539 / 250000000) (Real.log (933 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (87940849 / 500000000) ≤ -Real.log (1000000 / 1192297) ∧
    -Real.log (1000000 / 1192297) ≤ (175881699 / 1000000000) := by
  have h := checkLog_sound (w := (192297 / 2192297)) (n := 12)
    (lo := (87940849 / 500000000)) (hi := (175881699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1192297 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1192297 / 1000000) = 1/(1000000 / 1192297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (87940849 / 500000000) (175881699 / 1000000000) (Real.log (1192297 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1192297 / 1000000) = -Real.log (1000000 / 1192297) := by
    rw [show ((1192297 / 1000000) : ℝ) = ((1000000 / 1192297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (106780431 / 500000000) ≤ -Real.log (807703 / 1000000) ∧
    -Real.log (807703 / 1000000) ≤ (213560863 / 1000000000) := by
  have h := checkLog_sound (w := (192297 / 1807703)) (n := 12)
    (lo := (106780431 / 500000000)) (hi := (213560863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 807703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 807703) = 1/(807703 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-213560863 / 1000000000) (-106780431 / 500000000) (Real.log (807703 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (176233897 / 1000000000) ≤ -Real.log (1000000 / 1192717) ∧
    -Real.log (1000000 / 1192717) ≤ (88116949 / 500000000) := by
  have h := checkLog_sound (w := (192717 / 2192717)) (n := 12)
    (lo := (176233897 / 1000000000)) (hi := (88116949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1192717 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1192717 / 1000000) = 1/(1000000 / 1192717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (176233897 / 1000000000) (88116949 / 500000000) (Real.log (1192717 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1192717 / 1000000) = -Real.log (1000000 / 1192717) := by
    rw [show ((1192717 / 1000000) : ℝ) = ((1000000 / 1192717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (21408099 / 100000000) ≤ -Real.log (807283 / 1000000) ∧
    -Real.log (807283 / 1000000) ≤ (214080991 / 1000000000) := by
  have h := checkLog_sound (w := (192717 / 1807283)) (n := 12)
    (lo := (21408099 / 100000000)) (hi := (214080991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 807283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 807283) = 1/(807283 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-214080991 / 1000000000) (-21408099 / 100000000) (Real.log (807283 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (128730009 / 1000000000) ≤ -Real.log (1000000 / 1137383) ∧
    -Real.log (1000000 / 1137383) ≤ (12873001 / 100000000) := by
  have h := checkLog_sound (w := (137383 / 2137383)) (n := 12)
    (lo := (128730009 / 1000000000)) (hi := (12873001 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1137383 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1137383 / 1000000) = 1/(1000000 / 1137383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (128730009 / 1000000000) (12873001 / 100000000) (Real.log (1137383 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1137383 / 1000000) = -Real.log (1000000 / 1137383) := by
    rw [show ((1137383 / 1000000) : ℝ) = ((1000000 / 1137383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (147784487 / 1000000000) ≤ -Real.log (862617 / 1000000) ∧
    -Real.log (862617 / 1000000) ≤ (18473061 / 125000000) := by
  have h := checkLog_sound (w := (137383 / 1862617)) (n := 12)
    (lo := (147784487 / 1000000000)) (hi := (18473061 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 862617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 862617) = 1/(862617 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-18473061 / 125000000) (-147784487 / 1000000000) (Real.log (862617 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (128999011 / 1000000000) ≤ -Real.log (1000000 / 1137689) ∧
    -Real.log (1000000 / 1137689) ≤ (32249753 / 250000000) := by
  have h := checkLog_sound (w := (137689 / 2137689)) (n := 12)
    (lo := (128999011 / 1000000000)) (hi := (32249753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1137689 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1137689 / 1000000) = 1/(1000000 / 1137689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (128999011 / 1000000000) (32249753 / 250000000) (Real.log (1137689 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1137689 / 1000000) = -Real.log (1000000 / 1137689) := by
    rw [show ((1137689 / 1000000) : ℝ) = ((1000000 / 1137689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (37034821 / 250000000) ≤ -Real.log (862311 / 1000000) ∧
    -Real.log (862311 / 1000000) ≤ (29627857 / 200000000) := by
  have h := checkLog_sound (w := (137689 / 1862311)) (n := 12)
    (lo := (37034821 / 250000000)) (hi := (29627857 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 862311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 862311) = 1/(862311 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-29627857 / 200000000) (-37034821 / 250000000) (Real.log (862311 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (278043953 / 500000000) ≤ -Real.log (976562500 / 1702965903) ∧
    -Real.log (976562500 / 1702965903) ≤ (556087907 / 1000000000) := by
  have h := checkLog_sound (w := (726403403 / 2679528403)) (n := 12)
    (lo := (278043953 / 500000000)) (hi := (556087907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1702965903 / 976562500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1702965903 / 976562500) = 1/(976562500 / 1702965903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (278043953 / 500000000) (556087907 / 1000000000) (Real.log (1702965903 / 976562500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1702965903 / 976562500) = -Real.log (976562500 / 1702965903) := by
    rw [show ((1702965903 / 976562500) : ℝ) = ((976562500 / 1702965903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (557352953 / 1000000000) ≤ -Real.log (500000000000 / 873022257979) ∧
    -Real.log (500000000000 / 873022257979) ≤ (278676477 / 500000000) := by
  have h := checkLog_sound (w := (373022257979 / 1373022257979)) (n := 12)
    (lo := (557352953 / 1000000000)) (hi := (278676477 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((873022257979 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(873022257979 / 500000000000) = 1/(500000000000 / 873022257979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (557352953 / 1000000000) (278676477 / 500000000) (Real.log (873022257979 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (873022257979 / 500000000000) = -Real.log (500000000000 / 873022257979) := by
    rw [show ((873022257979 / 500000000000) : ℝ) = ((500000000000 / 873022257979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (152126 / 390625) ≤ -Real.log (500000000000 / 738078848289) ∧
    -Real.log (500000000000 / 738078848289) ≤ (389442561 / 1000000000) := by
  have h := checkLog_sound (w := (238078848289 / 1238078848289)) (n := 12)
    (lo := (152126 / 390625)) (hi := (389442561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((738078848289 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(738078848289 / 500000000000) = 1/(500000000000 / 738078848289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (152126 / 390625) (389442561 / 1000000000) (Real.log (738078848289 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (738078848289 / 500000000000) = -Real.log (500000000000 / 738078848289) := by
    rw [show ((738078848289 / 500000000000) : ℝ) = ((500000000000 / 738078848289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (48789361 / 125000000) ≤ -Real.log (50000000000 / 73872297571) ∧
    -Real.log (50000000000 / 73872297571) ≤ (390314889 / 1000000000) := by
  have h := checkLog_sound (w := (23872297571 / 123872297571)) (n := 12)
    (lo := (48789361 / 125000000)) (hi := (390314889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73872297571 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73872297571 / 50000000000) = 1/(50000000000 / 73872297571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (48789361 / 125000000) (390314889 / 1000000000) (Real.log (73872297571 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (73872297571 / 50000000000) = -Real.log (50000000000 / 73872297571) := by
    rw [show ((73872297571 / 50000000000) : ℝ) = ((50000000000 / 73872297571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (4320539 / 15625000) ≤ -Real.log (62500000000 / 82407879163) ∧
    -Real.log (62500000000 / 82407879163) ≤ (276514497 / 1000000000) := by
  have h := checkLog_sound (w := (19907879163 / 144907879163)) (n := 12)
    (lo := (4320539 / 15625000)) (hi := (276514497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82407879163 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82407879163 / 62500000000) = 1/(62500000000 / 82407879163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4320539 / 15625000) (276514497 / 1000000000) (Real.log (82407879163 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (82407879163 / 62500000000) = -Real.log (62500000000 / 82407879163) := by
    rw [show ((82407879163 / 62500000000) : ℝ) = ((62500000000 / 82407879163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (34642287 / 125000000) ≤ -Real.log (500000000000 / 659674409813) ∧
    -Real.log (500000000000 / 659674409813) ≤ (277138297 / 1000000000) := by
  have h := checkLog_sound (w := (159674409813 / 1159674409813)) (n := 12)
    (lo := (34642287 / 125000000)) (hi := (277138297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((659674409813 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(659674409813 / 500000000000) = 1/(500000000000 / 659674409813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (34642287 / 125000000) (277138297 / 1000000000) (Real.log (659674409813 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (659674409813 / 500000000000) = -Real.log (500000000000 / 659674409813) := by
    rw [show ((659674409813 / 500000000000) : ℝ) = ((500000000000 / 659674409813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1196267 / 62500000) ≤ -Real.log (981041739279 / 1000000000000) ∧
    -Real.log (981041739279 / 1000000000000) ≤ (19140273 / 1000000000) := by
  have h := checkLog_sound (w := (18958260721 / 1981041739279)) (n := 12)
    (lo := (1196267 / 62500000)) (hi := (19140273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981041739279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981041739279) = 1/(981041739279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-19140273 / 1000000000) (-1196267 / 62500000) (Real.log (981041739279 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (19054477 / 1000000000) ≤ -Real.log (981125911311 / 1000000000000) ∧
    -Real.log (981125911311 / 1000000000000) ≤ (9527239 / 500000000) := by
  have h := checkLog_sound (w := (18874088689 / 1981125911311)) (n := 12)
    (lo := (19054477 / 1000000000)) (hi := (9527239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981125911311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981125911311) = 1/(981125911311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-9527239 / 500000000) (-19054477 / 1000000000) (Real.log (981125911311 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell036
