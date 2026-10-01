import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell035
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

theorem reflection_log_1_neg : (959511 / 4000000) ≤ -Real.log (1280 / 1627) ∧
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


theorem reflection_log_1 : Bounds (959511 / 4000000) (239877751 / 1000000000) (Real.log (1627 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1627 / 1280) = -Real.log (1280 / 1627) := by
    rw [show ((1627 / 1280) : ℝ) = ((1280 / 1627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (79052539 / 250000000) ≤ -Real.log (933 / 1280) ∧
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


theorem reflection_log_2 : Bounds (-316210157 / 1000000000) (-79052539 / 250000000) (Real.log (933 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (7481771 / 31250000) ≤ -Real.log (1024 / 1301) ∧
    -Real.log (1024 / 1301) ≤ (239416673 / 1000000000) := by
  have h := checkLog_sound (w := (277 / 2325)) (n := 12)
    (lo := (7481771 / 31250000)) (hi := (239416673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1301 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1301 / 1024) = 1/(1024 / 1301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (7481771 / 31250000) (239416673 / 1000000000) (Real.log (1301 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1301 / 1024) = -Real.log (1024 / 1301) := by
    rw [show ((1301 / 1024) : ℝ) = ((1024 / 1301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (15770331 / 50000000) ≤ -Real.log (747 / 1024) ∧
    -Real.log (747 / 1024) ≤ (315406621 / 1000000000) := by
  have h := checkLog_sound (w := (277 / 1771)) (n := 12)
    (lo := (15770331 / 50000000)) (hi := (315406621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 747) = 1/(747 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-315406621 / 1000000000) (-15770331 / 50000000) (Real.log (747 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (175531053 / 1000000000) ≤ -Real.log (1000000 / 1191879) ∧
    -Real.log (1000000 / 1191879) ≤ (87765527 / 500000000) := by
  have h := checkLog_sound (w := (191879 / 2191879)) (n := 12)
    (lo := (175531053 / 1000000000)) (hi := (87765527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1191879 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1191879 / 1000000) = 1/(1000000 / 1191879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (175531053 / 1000000000) (87765527 / 500000000) (Real.log (1191879 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1191879 / 1000000) = -Real.log (1000000 / 1191879) := by
    rw [show ((1191879 / 1000000) : ℝ) = ((1000000 / 1191879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (213043479 / 1000000000) ≤ -Real.log (808121 / 1000000) ∧
    -Real.log (808121 / 1000000) ≤ (5326087 / 25000000) := by
  have h := checkLog_sound (w := (191879 / 1808121)) (n := 12)
    (lo := (213043479 / 1000000000)) (hi := (5326087 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 808121) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 808121) = 1/(808121 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-5326087 / 25000000) (-213043479 / 1000000000) (Real.log (808121 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (175882537 / 1000000000) ≤ -Real.log (500000 / 596149) ∧
    -Real.log (500000 / 596149) ≤ (87941269 / 500000000) := by
  have h := checkLog_sound (w := (96149 / 1096149)) (n := 12)
    (lo := (175882537 / 1000000000)) (hi := (87941269 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596149 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596149 / 500000) = 1/(500000 / 596149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (175882537 / 1000000000) (87941269 / 500000000) (Real.log (596149 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (596149 / 500000) = -Real.log (500000 / 596149) := by
    rw [show ((596149 / 500000) : ℝ) = ((500000 / 596149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2135621 / 10000000) ≤ -Real.log (403851 / 500000) ∧
    -Real.log (403851 / 500000) ≤ (213562101 / 1000000000) := by
  have h := checkLog_sound (w := (96149 / 903851)) (n := 12)
    (lo := (2135621 / 10000000)) (hi := (213562101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 403851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 403851) = 1/(403851 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-213562101 / 1000000000) (-2135621 / 10000000) (Real.log (403851 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (128461813 / 1000000000) ≤ -Real.log (500000 / 568539) ∧
    -Real.log (500000 / 568539) ≤ (64230907 / 500000000) := by
  have h := checkLog_sound (w := (68539 / 1068539)) (n := 12)
    (lo := (128461813 / 1000000000)) (hi := (64230907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((568539 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(568539 / 500000) = 1/(500000 / 568539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (128461813 / 1000000000) (64230907 / 500000000) (Real.log (568539 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (568539 / 500000) = -Real.log (500000 / 568539) := by
    rw [show ((568539 / 500000) : ℝ) = ((500000 / 568539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (73715487 / 500000000) ≤ -Real.log (431461 / 500000) ∧
    -Real.log (431461 / 500000) ≤ (5897239 / 40000000) := by
  have h := checkLog_sound (w := (68539 / 931461)) (n := 12)
    (lo := (73715487 / 500000000)) (hi := (5897239 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 431461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 431461) = 1/(431461 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-5897239 / 40000000) (-73715487 / 500000000) (Real.log (431461 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (16091361 / 125000000) ≤ -Real.log (125000 / 142173) ∧
    -Real.log (125000 / 142173) ≤ (128730889 / 1000000000) := by
  have h := checkLog_sound (w := (17173 / 267173)) (n := 12)
    (lo := (16091361 / 125000000)) (hi := (128730889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142173 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142173 / 125000) = 1/(125000 / 142173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (16091361 / 125000000) (128730889 / 1000000000) (Real.log (142173 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (142173 / 125000) = -Real.log (125000 / 142173) := by
    rw [show ((142173 / 125000) : ℝ) = ((125000 / 142173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (73892823 / 500000000) ≤ -Real.log (107827 / 125000) ∧
    -Real.log (107827 / 125000) ≤ (147785647 / 1000000000) := by
  have h := checkLog_sound (w := (17173 / 232827)) (n := 12)
    (lo := (73892823 / 500000000)) (hi := (147785647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 107827) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 107827) = 1/(107827 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-147785647 / 1000000000) (-73892823 / 500000000) (Real.log (107827 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (554823293 / 1000000000) ≤ -Real.log (125000000000 / 217704149933) ∧
    -Real.log (125000000000 / 217704149933) ≤ (277411647 / 500000000) := by
  have h := checkLog_sound (w := (92704149933 / 342704149933)) (n := 12)
    (lo := (554823293 / 1000000000)) (hi := (277411647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217704149933 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217704149933 / 125000000000) = 1/(125000000000 / 217704149933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (554823293 / 1000000000) (277411647 / 500000000) (Real.log (217704149933 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (217704149933 / 125000000000) = -Real.log (125000000000 / 217704149933) := by
    rw [show ((217704149933 / 125000000000) : ℝ) = ((125000000000 / 217704149933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (278043953 / 500000000) ≤ -Real.log (500000000000 / 871918542337) ∧
    -Real.log (500000000000 / 871918542337) ≤ (556087907 / 1000000000) := by
  have h := checkLog_sound (w := (371918542337 / 1371918542337)) (n := 12)
    (lo := (278043953 / 500000000)) (hi := (556087907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((871918542337 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(871918542337 / 500000000000) = 1/(500000000000 / 871918542337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (278043953 / 500000000) (556087907 / 1000000000) (Real.log (871918542337 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (871918542337 / 500000000000) = -Real.log (500000000000 / 871918542337) := by
    rw [show ((871918542337 / 500000000000) : ℝ) = ((500000000000 / 871918542337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (97143633 / 250000000) ≤ -Real.log (62500000000 / 92179806613) ∧
    -Real.log (62500000000 / 92179806613) ≤ (388574533 / 1000000000) := by
  have h := checkLog_sound (w := (29679806613 / 154679806613)) (n := 12)
    (lo := (97143633 / 250000000)) (hi := (388574533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92179806613 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(92179806613 / 62500000000) = 1/(62500000000 / 92179806613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (97143633 / 250000000) (388574533 / 1000000000) (Real.log (92179806613 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (92179806613 / 62500000000) = -Real.log (62500000000 / 92179806613) := by
    rw [show ((92179806613 / 62500000000) : ℝ) = ((62500000000 / 92179806613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (389444637 / 1000000000) ≤ -Real.log (500000000000 / 738080381131) ∧
    -Real.log (500000000000 / 738080381131) ≤ (194722319 / 500000000) := by
  have h := checkLog_sound (w := (238080381131 / 1238080381131)) (n := 12)
    (lo := (389444637 / 1000000000)) (hi := (194722319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((738080381131 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(738080381131 / 500000000000) = 1/(500000000000 / 738080381131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (389444637 / 1000000000) (194722319 / 500000000) (Real.log (738080381131 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (738080381131 / 500000000000) = -Real.log (500000000000 / 738080381131) := by
    rw [show ((738080381131 / 500000000000) : ℝ) = ((500000000000 / 738080381131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (68973197 / 250000000) ≤ -Real.log (500000000000 / 658853291491) ∧
    -Real.log (500000000000 / 658853291491) ≤ (275892789 / 1000000000) := by
  have h := checkLog_sound (w := (158853291491 / 1158853291491)) (n := 12)
    (lo := (68973197 / 250000000)) (hi := (275892789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((658853291491 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(658853291491 / 500000000000) = 1/(500000000000 / 658853291491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (68973197 / 250000000) (275892789 / 1000000000) (Real.log (658853291491 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (658853291491 / 500000000000) = -Real.log (500000000000 / 658853291491) := by
    rw [show ((658853291491 / 500000000000) : ℝ) = ((500000000000 / 658853291491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (138258267 / 500000000) ≤ -Real.log (500000000000 / 659264377197) ∧
    -Real.log (500000000000 / 659264377197) ≤ (55303307 / 200000000) := by
  have h := checkLog_sound (w := (159264377197 / 1159264377197)) (n := 12)
    (lo := (138258267 / 500000000)) (hi := (55303307 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((659264377197 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(659264377197 / 500000000000) = 1/(500000000000 / 659264377197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (138258267 / 500000000) (55303307 / 200000000) (Real.log (659264377197 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (659264377197 / 500000000000) = -Real.log (500000000000 / 659264377197) := by
    rw [show ((659264377197 / 500000000000) : ℝ) = ((500000000000 / 659264377197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (19054757 / 1000000000) ≤ -Real.log (15330088071 / 15625000000) ∧
    -Real.log (15330088071 / 15625000000) ≤ (9527379 / 500000000) := by
  have h := checkLog_sound (w := (294911929 / 30955088071)) (n := 12)
    (lo := (19054757 / 1000000000)) (hi := (9527379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15330088071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15330088071) = 1/(15330088071 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-9527379 / 500000000) (-19054757 / 1000000000) (Real.log (15330088071 / 15625000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (474229 / 25000000) ≤ -Real.log (245302405479 / 250000000000) ∧
    -Real.log (245302405479 / 250000000000) ≤ (18969161 / 1000000000) := by
  have h := checkLog_sound (w := (4697594521 / 495302405479)) (n := 12)
    (lo := (474229 / 25000000)) (hi := (18969161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245302405479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245302405479) = 1/(245302405479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-18969161 / 1000000000) (-474229 / 25000000) (Real.log (245302405479 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell035
