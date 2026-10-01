import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell052
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

theorem reflection_log_1_neg : (247683713 / 1000000000) ≤ -Real.log (5120 / 6559) ∧
    -Real.log (5120 / 6559) ≤ (123841857 / 500000000) := by
  have h := checkLog_sound (w := (1439 / 11679)) (n := 12)
    (lo := (247683713 / 1000000000)) (hi := (123841857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6559 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6559 / 5120) = 1/(5120 / 6559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (247683713 / 1000000000) (123841857 / 500000000) (Real.log (6559 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6559 / 5120) = -Real.log (5120 / 6559) := by
    rw [show ((6559 / 5120) : ℝ) = ((5120 / 6559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (5155781 / 15625000) ≤ -Real.log (3681 / 5120) ∧
    -Real.log (3681 / 5120) ≤ (65993997 / 200000000) := by
  have h := checkLog_sound (w := (1439 / 8801)) (n := 12)
    (lo := (5155781 / 15625000)) (hi := (65993997 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3681) = 1/(3681 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-65993997 / 200000000) (-5155781 / 15625000) (Real.log (3681 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (247226221 / 1000000000) ≤ -Real.log (1280 / 1639) ∧
    -Real.log (1280 / 1639) ≤ (123613111 / 500000000) := by
  have h := checkLog_sound (w := (359 / 2919)) (n := 12)
    (lo := (247226221 / 1000000000)) (hi := (123613111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1639 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1639 / 1280) = 1/(1280 / 1639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (247226221 / 1000000000) (123613111 / 500000000) (Real.log (1639 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1639 / 1280) = -Real.log (1280 / 1639) := by
    rw [show ((1639 / 1280) : ℝ) = ((1280 / 1639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (8228883 / 25000000) ≤ -Real.log (921 / 1280) ∧
    -Real.log (921 / 1280) ≤ (329155321 / 1000000000) := by
  have h := checkLog_sound (w := (359 / 2201)) (n := 12)
    (lo := (8228883 / 25000000)) (hi := (329155321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 921) = 1/(921 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-329155321 / 1000000000) (-8228883 / 25000000) (Real.log (921 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (181482037 / 1000000000) ≤ -Real.log (1000000 / 1198993) ∧
    -Real.log (1000000 / 1198993) ≤ (90741019 / 500000000) := by
  have h := checkLog_sound (w := (198993 / 2198993)) (n := 12)
    (lo := (181482037 / 1000000000)) (hi := (90741019 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1198993 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1198993 / 1000000) = 1/(1000000 / 1198993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (181482037 / 1000000000) (90741019 / 500000000) (Real.log (1198993 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1198993 / 1000000) = -Real.log (1000000 / 1198993) := by
    rw [show ((1198993 / 1000000) : ℝ) = ((1000000 / 1198993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (27735699 / 125000000) ≤ -Real.log (801007 / 1000000) ∧
    -Real.log (801007 / 1000000) ≤ (221885593 / 1000000000) := by
  have h := checkLog_sound (w := (198993 / 1801007)) (n := 12)
    (lo := (27735699 / 125000000)) (hi := (221885593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 801007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 801007) = 1/(801007 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-221885593 / 1000000000) (-27735699 / 125000000) (Real.log (801007 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (18183227 / 100000000) ≤ -Real.log (1000000 / 1199413) ∧
    -Real.log (1000000 / 1199413) ≤ (181832271 / 1000000000) := by
  have h := checkLog_sound (w := (199413 / 2199413)) (n := 12)
    (lo := (18183227 / 100000000)) (hi := (181832271 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1199413 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1199413 / 1000000) = 1/(1000000 / 1199413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (18183227 / 100000000) (181832271 / 1000000000) (Real.log (1199413 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1199413 / 1000000) = -Real.log (1000000 / 1199413) := by
    rw [show ((1199413 / 1000000) : ℝ) = ((1000000 / 1199413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (22241007 / 100000000) ≤ -Real.log (800587 / 1000000) ∧
    -Real.log (800587 / 1000000) ≤ (222410071 / 1000000000) := by
  have h := checkLog_sound (w := (199413 / 1800587)) (n := 12)
    (lo := (22241007 / 100000000)) (hi := (222410071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 800587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 800587) = 1/(800587 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-222410071 / 1000000000) (-22241007 / 100000000) (Real.log (800587 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (13301751 / 100000000) ≤ -Real.log (100000 / 114227) ∧
    -Real.log (100000 / 114227) ≤ (133017511 / 1000000000) := by
  have h := checkLog_sound (w := (14227 / 214227)) (n := 12)
    (lo := (13301751 / 100000000)) (hi := (133017511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((114227 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(114227 / 100000) = 1/(100000 / 114227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (13301751 / 100000000) (133017511 / 1000000000) (Real.log (114227 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (114227 / 100000) = -Real.log (100000 / 114227) := by
    rw [show ((114227 / 100000) : ℝ) = ((100000 / 114227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (76732957 / 500000000) ≤ -Real.log (85773 / 100000) ∧
    -Real.log (85773 / 100000) ≤ (30693183 / 200000000) := by
  have h := checkLog_sound (w := (14227 / 185773)) (n := 12)
    (lo := (76732957 / 500000000)) (hi := (30693183 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 85773) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 85773) = 1/(85773 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-30693183 / 200000000) (-76732957 / 500000000) (Real.log (85773 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (133286237 / 1000000000) ≤ -Real.log (1000000 / 1142577) ∧
    -Real.log (1000000 / 1142577) ≤ (66643119 / 500000000) := by
  have h := checkLog_sound (w := (142577 / 2142577)) (n := 12)
    (lo := (133286237 / 1000000000)) (hi := (66643119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1142577 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1142577 / 1000000) = 1/(1000000 / 1142577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (133286237 / 1000000000) (66643119 / 500000000) (Real.log (1142577 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1142577 / 1000000) = -Real.log (1000000 / 1142577) := by
    rw [show ((1142577 / 1000000) : ℝ) = ((1000000 / 1142577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (153823899 / 1000000000) ≤ -Real.log (857423 / 1000000) ∧
    -Real.log (857423 / 1000000) ≤ (1538239 / 10000000) := by
  have h := checkLog_sound (w := (142577 / 1857423)) (n := 12)
    (lo := (153823899 / 1000000000)) (hi := (1538239 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 857423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 857423) = 1/(857423 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1538239 / 10000000) (-153823899 / 1000000000) (Real.log (857423 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (288190771 / 500000000) ≤ -Real.log (500000000000 / 889793702497) ∧
    -Real.log (500000000000 / 889793702497) ≤ (576381543 / 1000000000) := by
  have h := checkLog_sound (w := (389793702497 / 1389793702497)) (n := 12)
    (lo := (288190771 / 500000000)) (hi := (576381543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((889793702497 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(889793702497 / 500000000000) = 1/(500000000000 / 889793702497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (288190771 / 500000000) (576381543 / 1000000000) (Real.log (889793702497 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (889793702497 / 500000000000) = -Real.log (500000000000 / 889793702497) := by
    rw [show ((889793702497 / 500000000000) : ℝ) = ((500000000000 / 889793702497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (577653697 / 1000000000) ≤ -Real.log (250000000000 / 445463189351) ∧
    -Real.log (250000000000 / 445463189351) ≤ (288826849 / 500000000) := by
  have h := checkLog_sound (w := (195463189351 / 695463189351)) (n := 12)
    (lo := (577653697 / 1000000000)) (hi := (288826849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((445463189351 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(445463189351 / 250000000000) = 1/(250000000000 / 445463189351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (577653697 / 1000000000) (288826849 / 500000000) (Real.log (445463189351 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (445463189351 / 250000000000) = -Real.log (250000000000 / 445463189351) := by
    rw [show ((445463189351 / 250000000000) : ℝ) = ((250000000000 / 445463189351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (40336763 / 100000000) ≤ -Real.log (250000000000 / 374214270287) ∧
    -Real.log (250000000000 / 374214270287) ≤ (403367631 / 1000000000) := by
  have h := checkLog_sound (w := (124214270287 / 624214270287)) (n := 12)
    (lo := (40336763 / 100000000)) (hi := (403367631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374214270287 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374214270287 / 250000000000) = 1/(250000000000 / 374214270287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (40336763 / 100000000) (403367631 / 1000000000) (Real.log (374214270287 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (374214270287 / 250000000000) = -Real.log (250000000000 / 374214270287) := by
    rw [show ((374214270287 / 250000000000) : ℝ) = ((250000000000 / 374214270287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (20212117 / 50000000) ≤ -Real.log (500000000000 / 749083484993) ∧
    -Real.log (500000000000 / 749083484993) ≤ (404242341 / 1000000000) := by
  have h := checkLog_sound (w := (249083484993 / 1249083484993)) (n := 12)
    (lo := (20212117 / 50000000)) (hi := (404242341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((749083484993 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(749083484993 / 500000000000) = 1/(500000000000 / 749083484993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (20212117 / 50000000) (404242341 / 1000000000) (Real.log (749083484993 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (749083484993 / 500000000000) = -Real.log (500000000000 / 749083484993) := by
    rw [show ((749083484993 / 500000000000) : ℝ) = ((500000000000 / 749083484993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (8952607 / 31250000) ≤ -Real.log (250000000000 / 332934023527) ∧
    -Real.log (250000000000 / 332934023527) ≤ (11459337 / 40000000) := by
  have h := checkLog_sound (w := (82934023527 / 582934023527)) (n := 12)
    (lo := (8952607 / 31250000)) (hi := (11459337 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((332934023527 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(332934023527 / 250000000000) = 1/(250000000000 / 332934023527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (8952607 / 31250000) (11459337 / 40000000) (Real.log (332934023527 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (332934023527 / 250000000000) = -Real.log (250000000000 / 332934023527) := by
    rw [show ((332934023527 / 250000000000) : ℝ) = ((250000000000 / 332934023527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (287110137 / 1000000000) ≤ -Real.log (250000000000 / 333142742847) ∧
    -Real.log (250000000000 / 333142742847) ≤ (143555069 / 500000000) := by
  have h := checkLog_sound (w := (83142742847 / 583142742847)) (n := 12)
    (lo := (287110137 / 1000000000)) (hi := (143555069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((333142742847 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(333142742847 / 250000000000) = 1/(250000000000 / 333142742847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (287110137 / 1000000000) (143555069 / 500000000) (Real.log (333142742847 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (333142742847 / 250000000000) = -Real.log (250000000000 / 333142742847) := by
    rw [show ((333142742847 / 250000000000) : ℝ) = ((250000000000 / 333142742847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (10268831 / 500000000) ≤ -Real.log (979671799071 / 1000000000000) ∧
    -Real.log (979671799071 / 1000000000000) ≤ (20537663 / 1000000000) := by
  have h := checkLog_sound (w := (20328200929 / 1979671799071)) (n := 12)
    (lo := (10268831 / 500000000)) (hi := (20537663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 979671799071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 979671799071) = 1/(979671799071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-20537663 / 1000000000) (-10268831 / 500000000) (Real.log (979671799071 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (20448403 / 1000000000) ≤ -Real.log (9797592471 / 10000000000) ∧
    -Real.log (9797592471 / 10000000000) ≤ (5112101 / 250000000) := by
  have h := checkLog_sound (w := (202407529 / 19797592471)) (n := 12)
    (lo := (20448403 / 1000000000)) (hi := (5112101 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9797592471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9797592471) = 1/(9797592471 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-5112101 / 250000000) (-20448403 / 1000000000) (Real.log (9797592471 / 10000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell052
