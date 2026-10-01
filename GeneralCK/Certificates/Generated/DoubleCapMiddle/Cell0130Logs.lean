import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0130
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

theorem reflection_log_1_neg : (76971683 / 250000000) ≤ -Real.log (2560 / 3483) ∧
    -Real.log (2560 / 3483) ≤ (307886733 / 1000000000) := by
  have h := checkLog_sound (w := (923 / 6043)) (n := 12)
    (lo := (76971683 / 250000000)) (hi := (307886733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3483 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3483 / 2560) = 1/(2560 / 3483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (76971683 / 250000000) (307886733 / 1000000000) (Real.log (3483 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3483 / 2560) = -Real.log (2560 / 3483) := by
    rw [show ((3483 / 2560) : ℝ) = ((2560 / 3483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (11178549 / 25000000) ≤ -Real.log (1637 / 2560) ∧
    -Real.log (1637 / 2560) ≤ (447141961 / 1000000000) := by
  have h := checkLog_sound (w := (923 / 4197)) (n := 12)
    (lo := (11178549 / 25000000)) (hi := (447141961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1637) = 1/(1637 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-447141961 / 1000000000) (-11178549 / 25000000) (Real.log (1637 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (61405007 / 200000000) ≤ -Real.log (64 / 87) ∧
    -Real.log (64 / 87) ≤ (76756259 / 250000000) := by
  have h := checkLog_sound (w := (23 / 151)) (n := 12)
    (lo := (61405007 / 200000000)) (hi := (76756259 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87 / 64) = 1/(64 / 87) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (61405007 / 200000000) (76756259 / 250000000) (Real.log (87 / 64)) := by
  have h := reflection_log_3_neg
  have he : Real.log (87 / 64) = -Real.log (64 / 87) := by
    rw [show ((87 / 64) : ℝ) = ((64 / 87) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (55663877 / 125000000) ≤ -Real.log (41 / 64) ∧
    -Real.log (41 / 64) ≤ (445311017 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 105)) (n := 12)
    (lo := (55663877 / 125000000)) (hi := (445311017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 41) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 41) = 1/(41 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-445311017 / 1000000000) (-55663877 / 125000000) (Real.log (41 / 64)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (542959989 / 1000000000) ≤ -Real.log (1280 / 2203) ∧
    -Real.log (1280 / 2203) ≤ (54295999 / 100000000) := by
  have h := checkLog_sound (w := (923 / 3483)) (n := 12)
    (lo := (542959989 / 1000000000)) (hi := (54295999 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2203 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2203 / 1280) = 1/(1280 / 2203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (542959989 / 1000000000) (54295999 / 100000000) (Real.log (2203 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2203 / 1280) = -Real.log (1280 / 2203) := by
    rw [show ((2203 / 1280) : ℝ) = ((1280 / 2203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (638439787 / 500000000) ≤ -Real.log (357 / 1280) ∧
    -Real.log (357 / 1280) ≤ (159609947 / 125000000) := by
  have h := checkLog_sound (w := (283 / 997)) (n := 12)
    (lo := (291866197 / 500000000)) (hi := (116746479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 357) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 357) = 1/(357 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-159609947 / 125000000) (-638439787 / 500000000) (Real.log (357 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (270798641 / 500000000) ≤ -Real.log (32 / 55) ∧
    -Real.log (32 / 55) ≤ (541597283 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 87)) (n := 12)
    (lo := (270798641 / 500000000)) (hi := (541597283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55 / 32) = 1/(32 / 55) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (270798641 / 500000000) (541597283 / 1000000000) (Real.log (55 / 32)) := by
  have h := reflection_log_7_neg
  have he : Real.log (55 / 32) = -Real.log (32 / 55) := by
    rw [show ((55 / 32) : ℝ) = ((32 / 55) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (317127831 / 250000000) ≤ -Real.log (9 / 32) ∧
    -Real.log (9 / 32) ≤ (634255663 / 500000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(16 / 9) = 1/(9 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-634255663 / 500000000) (-317127831 / 250000000) (Real.log (9 / 32)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (42036817 / 100000000) ≤ -Real.log (500000 / 761261) ∧
    -Real.log (500000 / 761261) ≤ (420368171 / 1000000000) := by
  have h := checkLog_sound (w := (261261 / 1261261)) (n := 12)
    (lo := (42036817 / 100000000)) (hi := (420368171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((761261 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(761261 / 500000) = 1/(500000 / 761261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (42036817 / 100000000) (420368171 / 1000000000) (Real.log (761261 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (761261 / 500000) = -Real.log (500000 / 761261) := by
    rw [show ((761261 / 500000) : ℝ) = ((500000 / 761261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (92404649 / 125000000) ≤ -Real.log (238739 / 500000) ∧
    -Real.log (238739 / 500000) ≤ (369618597 / 500000000) := by
  have h := checkLog_sound (w := (11261 / 488739)) (n := 12)
    (lo := (11522503 / 250000000)) (hi := (46090013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 238739) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 238739) = 1/(238739 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-369618597 / 500000000) (-92404649 / 125000000) (Real.log (238739 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (421570057 / 1000000000) ≤ -Real.log (1000000 / 1524353) ∧
    -Real.log (1000000 / 1524353) ≤ (210785029 / 500000000) := by
  have h := checkLog_sound (w := (524353 / 2524353)) (n := 12)
    (lo := (421570057 / 1000000000)) (hi := (210785029 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1524353 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1524353 / 1000000) = 1/(1000000 / 1524353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (421570057 / 1000000000) (210785029 / 500000000) (Real.log (1524353 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1524353 / 1000000) = -Real.log (1000000 / 1524353) := by
    rw [show ((1524353 / 1000000) : ℝ) = ((1000000 / 1524353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (148615859 / 200000000) ≤ -Real.log (475647 / 1000000) ∧
    -Real.log (475647 / 1000000) ≤ (743079297 / 1000000000) := by
  have h := checkLog_sound (w := (24353 / 975647)) (n := 12)
    (lo := (9986423 / 200000000)) (hi := (12483029 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 475647) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 475647) = 1/(475647 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-743079297 / 1000000000) (-148615859 / 200000000) (Real.log (475647 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (336146469 / 1000000000) ≤ -Real.log (125000 / 174943) ∧
    -Real.log (125000 / 174943) ≤ (33614647 / 100000000) := by
  have h := checkLog_sound (w := (49943 / 299943)) (n := 12)
    (lo := (336146469 / 1000000000)) (hi := (33614647 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((174943 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(174943 / 125000) = 1/(125000 / 174943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (336146469 / 1000000000) (33614647 / 100000000) (Real.log (174943 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (174943 / 125000) = -Real.log (125000 / 174943) := by
    rw [show ((174943 / 125000) : ℝ) = ((125000 / 174943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (63758239 / 125000000) ≤ -Real.log (75057 / 125000) ∧
    -Real.log (75057 / 125000) ≤ (510065913 / 1000000000) := by
  have h := checkLog_sound (w := (49943 / 200057)) (n := 12)
    (lo := (63758239 / 125000000)) (hi := (510065913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 75057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 75057) = 1/(75057 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-510065913 / 1000000000) (-63758239 / 125000000) (Real.log (75057 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (337309029 / 1000000000) ≤ -Real.log (250000 / 350293) ∧
    -Real.log (250000 / 350293) ≤ (33730903 / 100000000) := by
  have h := checkLog_sound (w := (100293 / 600293)) (n := 12)
    (lo := (337309029 / 1000000000)) (hi := (33730903 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((350293 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(350293 / 250000) = 1/(250000 / 350293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (337309029 / 1000000000) (33730903 / 100000000) (Real.log (350293 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (350293 / 250000) = -Real.log (250000 / 350293) := by
    rw [show ((350293 / 250000) : ℝ) = ((250000 / 350293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (512780867 / 1000000000) ≤ -Real.log (149707 / 250000) ∧
    -Real.log (149707 / 250000) ≤ (128195217 / 250000000) := by
  have h := checkLog_sound (w := (100293 / 399707)) (n := 12)
    (lo := (512780867 / 1000000000)) (hi := (128195217 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 149707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 149707) = 1/(149707 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-128195217 / 250000000) (-512780867 / 1000000000) (Real.log (149707 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1159605363 / 1000000000) ≤ -Real.log (20000000000 / 63773493229) ∧
    -Real.log (20000000000 / 63773493229) ≤ (231921073 / 200000000) := by
  have h := checkLog_sound (w := (23773493229 / 103773493229)) (n := 12)
    (lo := (466458183 / 1000000000)) (hi := (58307273 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63773493229 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(63773493229 / 40000000000) = 1/(20000000000 / 63773493229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1159605363 / 1000000000) (231921073 / 200000000) (Real.log (63773493229 / 20000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (63773493229 / 20000000000) = -Real.log (20000000000 / 63773493229) := by
    rw [show ((63773493229 / 20000000000) : ℝ) = ((20000000000 / 63773493229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1164649353 / 1000000000) ≤ -Real.log (250000000000 / 801199734257) ∧
    -Real.log (250000000000 / 801199734257) ≤ (232929871 / 200000000) := by
  have h := checkLog_sound (w := (301199734257 / 1301199734257)) (n := 12)
    (lo := (471502173 / 1000000000)) (hi := (235751087 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((801199734257 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(801199734257 / 500000000000) = 1/(250000000000 / 801199734257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1164649353 / 1000000000) (232929871 / 200000000) (Real.log (801199734257 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (801199734257 / 250000000000) = -Real.log (250000000000 / 801199734257) := by
    rw [show ((801199734257 / 250000000000) : ℝ) = ((250000000000 / 801199734257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (846212381 / 1000000000) ≤ -Real.log (100000000000 / 233080192387) ∧
    -Real.log (100000000000 / 233080192387) ≤ (846212383 / 1000000000) := by
  have h := checkLog_sound (w := (33080192387 / 433080192387)) (n := 12)
    (lo := (153065201 / 1000000000)) (hi := (76532601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233080192387 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(233080192387 / 200000000000) = 1/(100000000000 / 233080192387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (846212381 / 1000000000) (846212383 / 1000000000) (Real.log (233080192387 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (233080192387 / 100000000000) = -Real.log (100000000000 / 233080192387) := by
    rw [show ((233080192387 / 100000000000) : ℝ) = ((100000000000 / 233080192387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (106261237 / 125000000) ≤ -Real.log (250000000000 / 584964296927) ∧
    -Real.log (250000000000 / 584964296927) ≤ (425044949 / 500000000) := by
  have h := checkLog_sound (w := (84964296927 / 1084964296927)) (n := 12)
    (lo := (39235679 / 250000000)) (hi := (156942717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584964296927 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(584964296927 / 500000000000) = 1/(250000000000 / 584964296927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (106261237 / 125000000) (425044949 / 500000000) (Real.log (584964296927 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (584964296927 / 250000000000) = -Real.log (250000000000 / 584964296927) := by
    rw [show ((584964296927 / 250000000000) : ℝ) = ((250000000000 / 584964296927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0130
