import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell065
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

theorem reflection_log_1_neg : (253612133 / 1000000000) ≤ -Real.log (2560 / 3299) ∧
    -Real.log (2560 / 3299) ≤ (126806067 / 500000000) := by
  have h := checkLog_sound (w := (739 / 5859)) (n := 12)
    (lo := (253612133 / 1000000000)) (hi := (126806067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3299 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3299 / 2560) = 1/(2560 / 3299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (253612133 / 1000000000) (126806067 / 500000000) (Real.log (3299 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3299 / 2560) = -Real.log (2560 / 3299) := by
    rw [show ((3299 / 2560) : ℝ) = ((2560 / 3299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (340621457 / 1000000000) ≤ -Real.log (1821 / 2560) ∧
    -Real.log (1821 / 2560) ≤ (170310729 / 500000000) := by
  have h := checkLog_sound (w := (739 / 4381)) (n := 12)
    (lo := (340621457 / 1000000000)) (hi := (170310729 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1821) = 1/(1821 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-170310729 / 500000000) (-340621457 / 1000000000) (Real.log (1821 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (253157347 / 1000000000) ≤ -Real.log (1024 / 1319) ∧
    -Real.log (1024 / 1319) ≤ (63289337 / 250000000) := by
  have h := checkLog_sound (w := (295 / 2343)) (n := 12)
    (lo := (253157347 / 1000000000)) (hi := (63289337 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1319 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1319 / 1024) = 1/(1024 / 1319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (253157347 / 1000000000) (63289337 / 250000000) (Real.log (1319 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1319 / 1024) = -Real.log (1024 / 1319) := by
    rw [show ((1319 / 1024) : ℝ) = ((1024 / 1319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (339798073 / 1000000000) ≤ -Real.log (729 / 1024) ∧
    -Real.log (729 / 1024) ≤ (169899037 / 500000000) := by
  have h := checkLog_sound (w := (295 / 1753)) (n := 12)
    (lo := (339798073 / 1000000000)) (hi := (169899037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 729) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 729) = 1/(729 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-169899037 / 500000000) (-339798073 / 1000000000) (Real.log (729 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (186012237 / 1000000000) ≤ -Real.log (1000000 / 1204437) ∧
    -Real.log (1000000 / 1204437) ≤ (93006119 / 500000000) := by
  have h := checkLog_sound (w := (204437 / 2204437)) (n := 12)
    (lo := (186012237 / 1000000000)) (hi := (93006119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1204437 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1204437 / 1000000) = 1/(1000000 / 1204437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (186012237 / 1000000000) (93006119 / 500000000) (Real.log (1204437 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1204437 / 1000000) = -Real.log (1000000 / 1204437) := by
    rw [show ((1204437 / 1000000) : ℝ) = ((1000000 / 1204437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (114352619 / 500000000) ≤ -Real.log (795563 / 1000000) ∧
    -Real.log (795563 / 1000000) ≤ (228705239 / 1000000000) := by
  have h := checkLog_sound (w := (204437 / 1795563)) (n := 12)
    (lo := (114352619 / 500000000)) (hi := (228705239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 795563) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 795563) = 1/(795563 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-228705239 / 1000000000) (-114352619 / 500000000) (Real.log (795563 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (186360887 / 1000000000) ≤ -Real.log (1000000 / 1204857) ∧
    -Real.log (1000000 / 1204857) ≤ (23295111 / 125000000) := by
  have h := checkLog_sound (w := (204857 / 2204857)) (n := 12)
    (lo := (186360887 / 1000000000)) (hi := (23295111 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1204857 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1204857 / 1000000) = 1/(1000000 / 1204857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (186360887 / 1000000000) (23295111 / 125000000) (Real.log (1204857 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1204857 / 1000000) = -Real.log (1000000 / 1204857) := by
    rw [show ((1204857 / 1000000) : ℝ) = ((1000000 / 1204857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (114616653 / 500000000) ≤ -Real.log (795143 / 1000000) ∧
    -Real.log (795143 / 1000000) ≤ (229233307 / 1000000000) := by
  have h := checkLog_sound (w := (204857 / 1795143)) (n := 12)
    (lo := (114616653 / 500000000)) (hi := (229233307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 795143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 795143) = 1/(795143 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-229233307 / 1000000000) (-114616653 / 500000000) (Real.log (795143 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (136497489 / 1000000000) ≤ -Real.log (250000 / 286563) ∧
    -Real.log (250000 / 286563) ≤ (13649749 / 100000000) := by
  have h := checkLog_sound (w := (36563 / 536563)) (n := 12)
    (lo := (136497489 / 1000000000)) (hi := (13649749 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((286563 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(286563 / 250000) = 1/(250000 / 286563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (136497489 / 1000000000) (13649749 / 100000000) (Real.log (286563 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (286563 / 250000) = -Real.log (250000 / 286563) := by
    rw [show ((286563 / 250000) : ℝ) = ((250000 / 286563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (15811921 / 100000000) ≤ -Real.log (213437 / 250000) ∧
    -Real.log (213437 / 250000) ≤ (158119211 / 1000000000) := by
  have h := checkLog_sound (w := (36563 / 463437)) (n := 12)
    (lo := (15811921 / 100000000)) (hi := (158119211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 213437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 213437) = 1/(213437 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-158119211 / 1000000000) (-15811921 / 100000000) (Real.log (213437 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (27353231 / 200000000) ≤ -Real.log (3125 / 3583) ∧
    -Real.log (3125 / 3583) ≤ (34191539 / 250000000) := by
  have h := checkLog_sound (w := (229 / 3354)) (n := 12)
    (lo := (27353231 / 200000000)) (hi := (34191539 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3583 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3583 / 3125) = 1/(3125 / 3583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (27353231 / 200000000) (34191539 / 250000000) (Real.log (3583 / 3125)) := by
  have h := reflection_log_11_neg
  have he : Real.log (3583 / 3125) = -Real.log (3125 / 3583) := by
    rw [show ((3583 / 3125) : ℝ) = ((3125 / 3583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (158480037 / 1000000000) ≤ -Real.log (2667 / 3125) ∧
    -Real.log (2667 / 3125) ≤ (79240019 / 500000000) := by
  have h := checkLog_sound (w := (229 / 2896)) (n := 12)
    (lo := (158480037 / 1000000000)) (hi := (79240019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 2667) = 1/(2667 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-79240019 / 500000000) (-158480037 / 1000000000) (Real.log (2667 / 3125)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (29647771 / 50000000) ≤ -Real.log (250000000000 / 452331961591) ∧
    -Real.log (250000000000 / 452331961591) ≤ (592955421 / 1000000000) := by
  have h := checkLog_sound (w := (202331961591 / 702331961591)) (n := 12)
    (lo := (29647771 / 50000000)) (hi := (592955421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((452331961591 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(452331961591 / 250000000000) = 1/(250000000000 / 452331961591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (29647771 / 50000000) (592955421 / 1000000000) (Real.log (452331961591 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (452331961591 / 250000000000) = -Real.log (250000000000 / 452331961591) := by
    rw [show ((452331961591 / 250000000000) : ℝ) = ((250000000000 / 452331961591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (594233591 / 1000000000) ≤ -Real.log (100000000000 / 181164195497) ∧
    -Real.log (100000000000 / 181164195497) ≤ (74279199 / 125000000) := by
  have h := checkLog_sound (w := (81164195497 / 281164195497)) (n := 12)
    (lo := (594233591 / 1000000000)) (hi := (74279199 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181164195497 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181164195497 / 100000000000) = 1/(100000000000 / 181164195497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (594233591 / 1000000000) (74279199 / 125000000) (Real.log (181164195497 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (181164195497 / 100000000000) = -Real.log (100000000000 / 181164195497) := by
    rw [show ((181164195497 / 100000000000) : ℝ) = ((100000000000 / 181164195497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (103679369 / 250000000) ≤ -Real.log (25000000000 / 37848573903) ∧
    -Real.log (25000000000 / 37848573903) ≤ (414717477 / 1000000000) := by
  have h := checkLog_sound (w := (12848573903 / 62848573903)) (n := 12)
    (lo := (103679369 / 250000000)) (hi := (414717477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37848573903 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37848573903 / 25000000000) = 1/(25000000000 / 37848573903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (103679369 / 250000000) (414717477 / 1000000000) (Real.log (37848573903 / 25000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (37848573903 / 25000000000) = -Real.log (25000000000 / 37848573903) := by
    rw [show ((37848573903 / 25000000000) : ℝ) = ((25000000000 / 37848573903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (415594193 / 1000000000) ≤ -Real.log (250000000000 / 378817709519) ∧
    -Real.log (250000000000 / 378817709519) ≤ (207797097 / 500000000) := by
  have h := checkLog_sound (w := (128817709519 / 628817709519)) (n := 12)
    (lo := (415594193 / 1000000000)) (hi := (207797097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((378817709519 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(378817709519 / 250000000000) = 1/(250000000000 / 378817709519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (415594193 / 1000000000) (207797097 / 500000000) (Real.log (378817709519 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (378817709519 / 250000000000) = -Real.log (250000000000 / 378817709519) := by
    rw [show ((378817709519 / 250000000000) : ℝ) = ((250000000000 / 378817709519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (2946167 / 10000000) ≤ -Real.log (250000000000 / 335652909289) ∧
    -Real.log (250000000000 / 335652909289) ≤ (294616701 / 1000000000) := by
  have h := checkLog_sound (w := (85652909289 / 585652909289)) (n := 12)
    (lo := (2946167 / 10000000)) (hi := (294616701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((335652909289 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(335652909289 / 250000000000) = 1/(250000000000 / 335652909289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2946167 / 10000000) (294616701 / 1000000000) (Real.log (335652909289 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (335652909289 / 250000000000) = -Real.log (250000000000 / 335652909289) := by
    rw [show ((335652909289 / 250000000000) : ℝ) = ((250000000000 / 335652909289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (295246193 / 1000000000) ≤ -Real.log (250000000000 / 335864266967) ∧
    -Real.log (250000000000 / 335864266967) ≤ (147623097 / 500000000) := by
  have h := checkLog_sound (w := (85864266967 / 585864266967)) (n := 12)
    (lo := (295246193 / 1000000000)) (hi := (147623097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((335864266967 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(335864266967 / 250000000000) = 1/(250000000000 / 335864266967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (295246193 / 1000000000) (147623097 / 500000000) (Real.log (335864266967 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (335864266967 / 250000000000) = -Real.log (250000000000 / 335864266967) := by
    rw [show ((335864266967 / 250000000000) : ℝ) = ((250000000000 / 335864266967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (10856941 / 500000000) ≤ -Real.log (9555861 / 9765625) ∧
    -Real.log (9555861 / 9765625) ≤ (21713883 / 1000000000) := by
  have h := checkLog_sound (w := (104882 / 9660743)) (n := 12)
    (lo := (10856941 / 500000000)) (hi := (21713883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9765625 / 9555861) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9765625 / 9555861) = 1/(9555861 / 9765625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-21713883 / 1000000000) (-10856941 / 500000000) (Real.log (9555861 / 9765625)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (21621721 / 1000000000) ≤ -Real.log (61163147031 / 62500000000) ∧
    -Real.log (61163147031 / 62500000000) ≤ (10810861 / 500000000) := by
  have h := checkLog_sound (w := (1336852969 / 123663147031)) (n := 12)
    (lo := (21621721 / 1000000000)) (hi := (10810861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61163147031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61163147031) = 1/(61163147031 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-10810861 / 500000000) (-21621721 / 1000000000) (Real.log (61163147031 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell065
