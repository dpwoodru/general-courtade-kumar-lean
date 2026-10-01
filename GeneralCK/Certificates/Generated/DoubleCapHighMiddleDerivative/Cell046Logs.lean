import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell046
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

theorem reflection_log_1_neg : (244935619 / 1000000000) ≤ -Real.log (5120 / 6541) ∧
    -Real.log (5120 / 6541) ≤ (12246781 / 50000000) := by
  have h := checkLog_sound (w := (1421 / 11661)) (n := 12)
    (lo := (244935619 / 1000000000)) (hi := (12246781 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6541 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6541 / 5120) = 1/(5120 / 6541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (244935619 / 1000000000) (12246781 / 50000000) (Real.log (6541 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6541 / 5120) = -Real.log (5120 / 6541) := by
    rw [show ((6541 / 5120) : ℝ) = ((5120 / 6541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (162545963 / 500000000) ≤ -Real.log (3699 / 5120) ∧
    -Real.log (3699 / 5120) ≤ (325091927 / 1000000000) := by
  have h := checkLog_sound (w := (1421 / 8819)) (n := 12)
    (lo := (162545963 / 500000000)) (hi := (325091927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3699) = 1/(3699 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-325091927 / 1000000000) (-162545963 / 500000000) (Real.log (3699 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (244476869 / 1000000000) ≤ -Real.log (2560 / 3269) ∧
    -Real.log (2560 / 3269) ≤ (24447687 / 100000000) := by
  have h := checkLog_sound (w := (709 / 5829)) (n := 12)
    (lo := (244476869 / 1000000000)) (hi := (24447687 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3269 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3269 / 2560) = 1/(2560 / 3269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (244476869 / 1000000000) (24447687 / 100000000) (Real.log (3269 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3269 / 2560) = -Real.log (2560 / 3269) := by
    rw [show ((3269 / 2560) : ℝ) = ((2560 / 3269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (40535153 / 125000000) ≤ -Real.log (1851 / 2560) ∧
    -Real.log (1851 / 2560) ≤ (12971249 / 40000000) := by
  have h := checkLog_sound (w := (709 / 4411)) (n := 12)
    (lo := (40535153 / 125000000)) (hi := (12971249 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1851) = 1/(1851 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-12971249 / 40000000) (-40535153 / 125000000) (Real.log (1851 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (44846187 / 250000000) ≤ -Real.log (1000000 / 1196481) ∧
    -Real.log (1000000 / 1196481) ≤ (179384749 / 1000000000) := by
  have h := checkLog_sound (w := (196481 / 2196481)) (n := 12)
    (lo := (44846187 / 250000000)) (hi := (179384749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1196481 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1196481 / 1000000) = 1/(1000000 / 1196481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (44846187 / 250000000) (179384749 / 1000000000) (Real.log (1196481 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1196481 / 1000000) = -Real.log (1000000 / 1196481) := by
    rw [show ((1196481 / 1000000) : ℝ) = ((1000000 / 1196481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (218754447 / 1000000000) ≤ -Real.log (803519 / 1000000) ∧
    -Real.log (803519 / 1000000) ≤ (13672153 / 62500000) := by
  have h := checkLog_sound (w := (196481 / 1803519)) (n := 12)
    (lo := (218754447 / 1000000000)) (hi := (13672153 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 803519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 803519) = 1/(803519 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-13672153 / 62500000) (-218754447 / 1000000000) (Real.log (803519 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (44933929 / 250000000) ≤ -Real.log (1000000 / 1196901) ∧
    -Real.log (1000000 / 1196901) ≤ (179735717 / 1000000000) := by
  have h := checkLog_sound (w := (196901 / 2196901)) (n := 12)
    (lo := (44933929 / 250000000)) (hi := (179735717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1196901 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1196901 / 1000000) = 1/(1000000 / 1196901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (44933929 / 250000000) (179735717 / 1000000000) (Real.log (1196901 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1196901 / 1000000) = -Real.log (1000000 / 1196901) := by
    rw [show ((1196901 / 1000000) : ℝ) = ((1000000 / 1196901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (54819321 / 250000000) ≤ -Real.log (803099 / 1000000) ∧
    -Real.log (803099 / 1000000) ≤ (43855457 / 200000000) := by
  have h := checkLog_sound (w := (196901 / 1803099)) (n := 12)
    (lo := (54819321 / 250000000)) (hi := (43855457 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 803099) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 803099) = 1/(803099 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-43855457 / 200000000) (-54819321 / 250000000) (Real.log (803099 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (26282129 / 200000000) ≤ -Real.log (250000 / 285109) ∧
    -Real.log (250000 / 285109) ≤ (65705323 / 500000000) := by
  have h := checkLog_sound (w := (35109 / 535109)) (n := 12)
    (lo := (26282129 / 200000000)) (hi := (65705323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((285109 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(285109 / 250000) = 1/(250000 / 285109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (26282129 / 200000000) (65705323 / 500000000) (Real.log (285109 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (285109 / 250000) = -Real.log (250000 / 285109) := by
    rw [show ((285109 / 250000) : ℝ) = ((250000 / 285109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (30265999 / 200000000) ≤ -Real.log (214891 / 250000) ∧
    -Real.log (214891 / 250000) ≤ (37832499 / 250000000) := by
  have h := checkLog_sound (w := (35109 / 464891)) (n := 12)
    (lo := (30265999 / 200000000)) (hi := (37832499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 214891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 214891) = 1/(214891 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-37832499 / 250000000) (-30265999 / 200000000) (Real.log (214891 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (131678927 / 1000000000) ≤ -Real.log (500000 / 570371) ∧
    -Real.log (500000 / 570371) ≤ (8229933 / 62500000) := by
  have h := checkLog_sound (w := (70371 / 1070371)) (n := 12)
    (lo := (131678927 / 1000000000)) (hi := (8229933 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((570371 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(570371 / 500000) = 1/(500000 / 570371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (131678927 / 1000000000) (8229933 / 62500000) (Real.log (570371 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (570371 / 500000) = -Real.log (500000 / 570371) := by
    rw [show ((570371 / 500000) : ℝ) = ((500000 / 570371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (37921513 / 250000000) ≤ -Real.log (429629 / 500000) ∧
    -Real.log (429629 / 500000) ≤ (151686053 / 1000000000) := by
  have h := checkLog_sound (w := (70371 / 929629)) (n := 12)
    (lo := (37921513 / 250000000)) (hi := (151686053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 429629) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 429629) = 1/(429629 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-151686053 / 1000000000) (-37921513 / 250000000) (Real.log (429629 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (284379047 / 500000000) ≤ -Real.log (10000000000 / 17660723933) ∧
    -Real.log (10000000000 / 17660723933) ≤ (113751619 / 200000000) := by
  have h := checkLog_sound (w := (7660723933 / 27660723933)) (n := 12)
    (lo := (284379047 / 500000000)) (hi := (113751619 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17660723933 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17660723933 / 10000000000) = 1/(10000000000 / 17660723933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (284379047 / 500000000) (113751619 / 200000000) (Real.log (17660723933 / 10000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (17660723933 / 10000000000) = -Real.log (10000000000 / 17660723933) := by
    rw [show ((17660723933 / 10000000000) : ℝ) = ((10000000000 / 17660723933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (285013773 / 500000000) ≤ -Real.log (500000000000 / 884157880509) ∧
    -Real.log (500000000000 / 884157880509) ≤ (570027547 / 1000000000) := by
  have h := checkLog_sound (w := (384157880509 / 1384157880509)) (n := 12)
    (lo := (285013773 / 500000000)) (hi := (570027547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((884157880509 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(884157880509 / 500000000000) = 1/(500000000000 / 884157880509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (285013773 / 500000000) (570027547 / 1000000000) (Real.log (884157880509 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (884157880509 / 500000000000) = -Real.log (500000000000 / 884157880509) := by
    rw [show ((884157880509 / 500000000000) : ℝ) = ((500000000000 / 884157880509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (99534799 / 250000000) ≤ -Real.log (125000000000 / 186131410707) ∧
    -Real.log (125000000000 / 186131410707) ≤ (398139197 / 1000000000) := by
  have h := checkLog_sound (w := (61131410707 / 311131410707)) (n := 12)
    (lo := (99534799 / 250000000)) (hi := (398139197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((186131410707 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(186131410707 / 125000000000) = 1/(125000000000 / 186131410707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (99534799 / 250000000) (398139197 / 1000000000) (Real.log (186131410707 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (186131410707 / 125000000000) = -Real.log (125000000000 / 186131410707) := by
    rw [show ((186131410707 / 125000000000) : ℝ) = ((125000000000 / 186131410707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (399013001 / 1000000000) ≤ -Real.log (500000000000 / 745176497543) ∧
    -Real.log (500000000000 / 745176497543) ≤ (199506501 / 500000000) := by
  have h := checkLog_sound (w := (245176497543 / 1245176497543)) (n := 12)
    (lo := (399013001 / 1000000000)) (hi := (199506501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((745176497543 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(745176497543 / 500000000000) = 1/(500000000000 / 745176497543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (399013001 / 1000000000) (199506501 / 500000000) (Real.log (745176497543 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (745176497543 / 500000000000) = -Real.log (500000000000 / 745176497543) := by
    rw [show ((745176497543 / 500000000000) : ℝ) = ((500000000000 / 745176497543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (1767129 / 6250000) ≤ -Real.log (250000000000 / 331690252267) ∧
    -Real.log (250000000000 / 331690252267) ≤ (282740641 / 1000000000) := by
  have h := checkLog_sound (w := (81690252267 / 581690252267)) (n := 12)
    (lo := (1767129 / 6250000)) (hi := (282740641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((331690252267 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(331690252267 / 250000000000) = 1/(250000000000 / 331690252267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1767129 / 6250000) (282740641 / 1000000000) (Real.log (331690252267 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (331690252267 / 250000000000) = -Real.log (250000000000 / 331690252267) := by
    rw [show ((331690252267 / 250000000000) : ℝ) = ((250000000000 / 331690252267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (14168249 / 50000000) ≤ -Real.log (50000000000 / 66379480901) ∧
    -Real.log (50000000000 / 66379480901) ≤ (283364981 / 1000000000) := by
  have h := checkLog_sound (w := (16379480901 / 116379480901)) (n := 12)
    (lo := (14168249 / 50000000)) (hi := (283364981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66379480901 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(66379480901 / 50000000000) = 1/(50000000000 / 66379480901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (14168249 / 50000000) (283364981 / 1000000000) (Real.log (66379480901 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (66379480901 / 50000000000) = -Real.log (50000000000 / 66379480901) := by
    rw [show ((66379480901 / 50000000000) : ℝ) = ((50000000000 / 66379480901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (5001781 / 250000000) ≤ -Real.log (245047922359 / 250000000000) ∧
    -Real.log (245047922359 / 250000000000) ≤ (160057 / 8000000) := by
  have h := checkLog_sound (w := (4952077641 / 495047922359)) (n := 12)
    (lo := (5001781 / 250000000)) (hi := (160057 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245047922359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245047922359) = 1/(245047922359 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-160057 / 8000000) (-5001781 / 250000000) (Real.log (245047922359 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (19919349 / 1000000000) ≤ -Real.log (61267358119 / 62500000000) ∧
    -Real.log (61267358119 / 62500000000) ≤ (398387 / 20000000) := by
  have h := checkLog_sound (w := (1232641881 / 123767358119)) (n := 12)
    (lo := (19919349 / 1000000000)) (hi := (398387 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61267358119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61267358119) = 1/(61267358119 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-398387 / 20000000) (-19919349 / 1000000000) (Real.log (61267358119 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell046
