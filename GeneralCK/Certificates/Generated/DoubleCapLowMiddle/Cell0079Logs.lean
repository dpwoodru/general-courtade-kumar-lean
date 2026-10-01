import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0079
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

theorem reflection_log_1_neg : (84422863 / 125000000) ≤ -Real.log (51200 / 100597) ∧
    -Real.log (51200 / 100597) ≤ (135076581 / 200000000) := by
  have h := checkLog_sound (w := (49397 / 151797)) (n := 12)
    (lo := (84422863 / 125000000)) (hi := (135076581 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100597 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100597 / 51200) = 1/(51200 / 100597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (84422863 / 125000000) (135076581 / 200000000) (Real.log (100597 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100597 / 51200) = -Real.log (51200 / 100597) := by
    rw [show ((100597 / 51200) : ℝ) = ((51200 / 100597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (669257517 / 200000000) ≤ -Real.log (1803 / 51200) ∧
    -Real.log (1803 / 51200) ≤ (334628759 / 100000000) := by
  have h := checkLog_sound (w := (1397 / 5003)) (n := 12)
    (lo := (114739773 / 200000000)) (hi := (286849433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1803) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1803) = 1/(1803 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-334628759 / 100000000) (-669257517 / 200000000) (Real.log (1803 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (675194013 / 1000000000) ≤ -Real.log (25600 / 50289) ∧
    -Real.log (25600 / 50289) ≤ (337597007 / 500000000) := by
  have h := checkLog_sound (w := (24689 / 75889)) (n := 12)
    (lo := (675194013 / 1000000000)) (hi := (337597007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50289 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50289 / 25600) = 1/(25600 / 50289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (675194013 / 1000000000) (337597007 / 500000000) (Real.log (50289 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (50289 / 25600) = -Real.log (25600 / 50289) := by
    rw [show ((50289 / 25600) : ℝ) = ((25600 / 50289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (333580473 / 100000000) ≤ -Real.log (911 / 25600) ∧
    -Real.log (911 / 25600) ≤ (667160947 / 200000000) := by
  have h := checkLog_sound (w := (689 / 2511)) (n := 12)
    (lo := (56321601 / 100000000)) (hi := (563216011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 911) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 911) = 1/(911 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-667160947 / 200000000) (-333580473 / 100000000) (Real.log (911 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (328648671 / 500000000) ≤ -Real.log (25600 / 49397) ∧
    -Real.log (25600 / 49397) ≤ (657297343 / 1000000000) := by
  have h := checkLog_sound (w := (23797 / 74997)) (n := 12)
    (lo := (328648671 / 500000000)) (hi := (657297343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49397 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49397 / 25600) = 1/(25600 / 49397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (328648671 / 500000000) (657297343 / 1000000000) (Real.log (49397 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49397 / 25600) = -Real.log (25600 / 49397) := by
    rw [show ((49397 / 25600) : ℝ) = ((25600 / 49397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (530628081 / 200000000) ≤ -Real.log (1803 / 25600) ∧
    -Real.log (1803 / 25600) ≤ (2653140409 / 1000000000) := by
  have h := checkLog_sound (w := (1397 / 5003)) (n := 12)
    (lo := (114739773 / 200000000)) (hi := (286849433 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1803) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1803) = 1/(1803 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2653140409 / 1000000000) (-530628081 / 200000000) (Real.log (1803 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (656912629 / 1000000000) ≤ -Real.log (12800 / 24689) ∧
    -Real.log (12800 / 24689) ≤ (65691263 / 100000000) := by
  have h := checkLog_sound (w := (11889 / 37489)) (n := 12)
    (lo := (656912629 / 1000000000)) (hi := (65691263 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24689 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24689 / 12800) = 1/(12800 / 24689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (656912629 / 1000000000) (65691263 / 100000000) (Real.log (24689 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24689 / 12800) = -Real.log (12800 / 24689) := by
    rw [show ((24689 / 12800) : ℝ) = ((12800 / 24689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (52853151 / 20000000) ≤ -Real.log (911 / 12800) ∧
    -Real.log (911 / 12800) ≤ (1321328777 / 500000000) := by
  have h := checkLog_sound (w := (689 / 2511)) (n := 12)
    (lo := (56321601 / 100000000)) (hi := (563216011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 911) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 911) = 1/(911 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1321328777 / 500000000) (-52853151 / 20000000) (Real.log (911 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (16957221 / 25000000) ≤ -Real.log (1000000 / 1970503) ∧
    -Real.log (1000000 / 1970503) ≤ (678288841 / 1000000000) := by
  have h := checkLog_sound (w := (970503 / 2970503)) (n := 12)
    (lo := (16957221 / 25000000)) (hi := (678288841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1970503 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1970503 / 1000000) = 1/(1000000 / 1970503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (16957221 / 25000000) (678288841 / 1000000000) (Real.log (1970503 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1970503 / 1000000) = -Real.log (1000000 / 1970503) := by
    rw [show ((1970503 / 1000000) : ℝ) = ((1000000 / 1970503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (440433339 / 125000000) ≤ -Real.log (29497 / 1000000) ∧
    -Real.log (29497 / 1000000) ≤ (1761733359 / 500000000) := by
  have h := checkLog_sound (w := (1753 / 60747)) (n := 12)
    (lo := (14432703 / 250000000)) (hi := (57730813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 29497) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 29497) = 1/(29497 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1761733359 / 500000000) (-440433339 / 125000000) (Real.log (29497 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (339218761 / 500000000) ≤ -Real.log (250000 / 492699) ∧
    -Real.log (250000 / 492699) ≤ (678437523 / 1000000000) := by
  have h := checkLog_sound (w := (242699 / 742699)) (n := 12)
    (lo := (339218761 / 500000000)) (hi := (678437523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((492699 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(492699 / 250000) = 1/(250000 / 492699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (339218761 / 500000000) (678437523 / 1000000000) (Real.log (492699 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (492699 / 250000) = -Real.log (250000 / 492699) := by
    rw [show ((492699 / 250000) : ℝ) = ((250000 / 492699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3533449589 / 1000000000) ≤ -Real.log (7301 / 250000) ∧
    -Real.log (7301 / 250000) ≤ (706689919 / 200000000) := by
  have h := checkLog_sound (w := (1023 / 30227)) (n := 12)
    (lo := (67713689 / 1000000000)) (hi := (6771369 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14602) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 14602) = 1/(7301 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-706689919 / 200000000) (-3533449589 / 1000000000) (Real.log (7301 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (169544043 / 250000000) ≤ -Real.log (1000000 / 1970281) ∧
    -Real.log (1000000 / 1970281) ≤ (678176173 / 1000000000) := by
  have h := checkLog_sound (w := (970281 / 2970281)) (n := 12)
    (lo := (169544043 / 250000000)) (hi := (678176173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1970281 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1970281 / 1000000) = 1/(1000000 / 1970281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (169544043 / 250000000) (678176173 / 1000000000) (Real.log (1970281 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1970281 / 1000000) = -Real.log (1000000 / 1970281) := by
    rw [show ((1970281 / 1000000) : ℝ) = ((1000000 / 1970281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (54937011 / 15625000) ≤ -Real.log (29719 / 1000000) ∧
    -Real.log (29719 / 1000000) ≤ (351596871 / 100000000) := by
  have h := checkLog_sound (w := (1531 / 60969)) (n := 12)
    (lo := (12558201 / 250000000)) (hi := (10046561 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 29719) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 29719) = 1/(29719 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-351596871 / 100000000) (-54937011 / 15625000) (Real.log (29719 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (6783269 / 10000000) ≤ -Real.log (500000 / 985289) ∧
    -Real.log (500000 / 985289) ≤ (678326901 / 1000000000) := by
  have h := checkLog_sound (w := (485289 / 1485289)) (n := 12)
    (lo := (6783269 / 10000000)) (hi := (678326901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((985289 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(985289 / 500000) = 1/(500000 / 985289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (6783269 / 10000000) (678326901 / 1000000000) (Real.log (985289 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (985289 / 500000) = -Real.log (500000 / 985289) := by
    rw [show ((985289 / 500000) : ℝ) = ((500000 / 985289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1763006291 / 500000000) ≤ -Real.log (14711 / 500000) ∧
    -Real.log (14711 / 500000) ≤ (881503147 / 250000000) := by
  have h := checkLog_sound (w := (457 / 15168)) (n := 12)
    (lo := (30138341 / 500000000)) (hi := (60276683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14711) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 14711) = 1/(14711 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-881503147 / 250000000) (-1763006291 / 500000000) (Real.log (14711 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (131304861 / 31250000) ≤ -Real.log (100000000000 / 6680350544123) ∧
    -Real.log (100000000000 / 6680350544123) ≤ (4201755559 / 1000000000) := by
  have h := checkLog_sound (w := (280350544123 / 13080350544123)) (n := 12)
    (lo := (5359059 / 125000000)) (hi := (42872473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6680350544123 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(6680350544123 / 6400000000000) = 1/(100000000000 / 6680350544123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (131304861 / 31250000) (4201755559 / 1000000000) (Real.log (6680350544123 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6680350544123 / 100000000000) = -Real.log (100000000000 / 6680350544123) := by
    rw [show ((6680350544123 / 100000000000) : ℝ) = ((100000000000 / 6680350544123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4211887111 / 1000000000) ≤ -Real.log (500000000000 / 33741884673333) ∧
    -Real.log (500000000000 / 33741884673333) ≤ (2105943559 / 500000000) := by
  have h := checkLog_sound (w := (1741884673333 / 65741884673333)) (n := 12)
    (lo := (53004031 / 1000000000)) (hi := (207047 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33741884673333 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(33741884673333 / 32000000000000) = 1/(500000000000 / 33741884673333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4211887111 / 1000000000) (2105943559 / 500000000) (Real.log (33741884673333 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (33741884673333 / 500000000000) = -Real.log (500000000000 / 33741884673333) := by
    rw [show ((33741884673333 / 500000000000) : ℝ) = ((500000000000 / 33741884673333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (33553159 / 8000000) ≤ -Real.log (125000000000 / 8287126922171) ∧
    -Real.log (125000000000 / 8287126922171) ≤ (2097072441 / 500000000) := by
  have h := checkLog_sound (w := (287126922171 / 16287126922171)) (n := 12)
    (lo := (7052359 / 200000000)) (hi := (8815449 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8287126922171 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(8287126922171 / 8000000000000) = 1/(125000000000 / 8287126922171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (33553159 / 8000000) (2097072441 / 500000000) (Real.log (8287126922171 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (8287126922171 / 125000000000) = -Real.log (125000000000 / 8287126922171) := by
    rw [show ((8287126922171 / 125000000000) : ℝ) = ((125000000000 / 8287126922171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (2102169741 / 500000000) ≤ -Real.log (62500000000 / 4186021514513) ∧
    -Real.log (62500000000 / 4186021514513) ≤ (4204339489 / 1000000000) := by
  have h := checkLog_sound (w := (186021514513 / 8186021514513)) (n := 12)
    (lo := (22728201 / 500000000)) (hi := (45456403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4186021514513 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4186021514513 / 4000000000000) = 1/(62500000000 / 4186021514513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (2102169741 / 500000000) (4204339489 / 1000000000) (Real.log (4186021514513 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (4186021514513 / 62500000000) = -Real.log (62500000000 / 4186021514513) := by
    rw [show ((4186021514513 / 62500000000) : ℝ) = ((62500000000 / 4186021514513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0079
