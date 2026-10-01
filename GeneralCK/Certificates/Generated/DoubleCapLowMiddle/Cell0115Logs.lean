import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0115
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

theorem reflection_log_1_neg : (41749351 / 62500000) ≤ -Real.log (3200 / 6241) ∧
    -Real.log (3200 / 6241) ≤ (667989617 / 1000000000) := by
  have h := checkLog_sound (w := (3041 / 9441)) (n := 12)
    (lo := (41749351 / 62500000)) (hi := (667989617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6241 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6241 / 3200) = 1/(3200 / 6241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (41749351 / 62500000) (667989617 / 1000000000) (Real.log (6241 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6241 / 3200) = -Real.log (3200 / 6241) := by
    rw [show ((6241 / 3200) : ℝ) = ((3200 / 6241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (750500471 / 250000000) ≤ -Real.log (159 / 3200) ∧
    -Real.log (159 / 3200) ≤ (3002001889 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 359)) (n := 12)
    (lo := (57353291 / 250000000)) (hi := (45882633 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 159) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(200 / 159) = 1/(159 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3002001889 / 1000000000) (-750500471 / 250000000) (Real.log (159 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (133521799 / 200000000) ≤ -Real.log (25600 / 49909) ∧
    -Real.log (25600 / 49909) ≤ (166902249 / 250000000) := by
  have h := checkLog_sound (w := (24309 / 75509)) (n := 12)
    (lo := (133521799 / 200000000)) (hi := (166902249 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49909 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49909 / 25600) = 1/(25600 / 49909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (133521799 / 200000000) (166902249 / 250000000) (Real.log (49909 / 25600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (49909 / 25600) = -Real.log (25600 / 49909) := by
    rw [show ((49909 / 25600) : ℝ) = ((25600 / 49909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2987175237 / 1000000000) ≤ -Real.log (1291 / 25600) ∧
    -Real.log (1291 / 25600) ≤ (1493587621 / 500000000) := by
  have h := checkLog_sound (w := (309 / 2891)) (n := 12)
    (lo := (214586517 / 1000000000)) (hi := (107293259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1291) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1291) = 1/(1291 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1493587621 / 500000000) (-2987175237 / 1000000000) (Real.log (1291 / 25600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (642182779 / 1000000000) ≤ -Real.log (1600 / 3041) ∧
    -Real.log (1600 / 3041) ≤ (32109139 / 50000000) := by
  have h := checkLog_sound (w := (1441 / 4641)) (n := 12)
    (lo := (642182779 / 1000000000)) (hi := (32109139 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3041 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3041 / 1600) = 1/(1600 / 3041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (642182779 / 1000000000) (32109139 / 50000000) (Real.log (3041 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3041 / 1600) = -Real.log (1600 / 3041) := by
    rw [show ((3041 / 1600) : ℝ) = ((1600 / 3041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (144303419 / 62500000) ≤ -Real.log (159 / 1600) ∧
    -Real.log (159 / 1600) ≤ (577213677 / 250000000) := by
  have h := checkLog_sound (w := (41 / 359)) (n := 12)
    (lo := (57353291 / 250000000)) (hi := (45882633 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 159) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(200 / 159) = 1/(159 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-577213677 / 250000000) (-144303419 / 62500000) (Real.log (159 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (641401481 / 1000000000) ≤ -Real.log (12800 / 24309) ∧
    -Real.log (12800 / 24309) ≤ (320700741 / 500000000) := by
  have h := checkLog_sound (w := (11509 / 37109)) (n := 12)
    (lo := (641401481 / 1000000000)) (hi := (320700741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24309 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24309 / 12800) = 1/(12800 / 24309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (641401481 / 1000000000) (320700741 / 500000000) (Real.log (24309 / 12800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (24309 / 12800) = -Real.log (12800 / 24309) := by
    rw [show ((24309 / 12800) : ℝ) = ((12800 / 24309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2294028057 / 1000000000) ≤ -Real.log (1291 / 12800) ∧
    -Real.log (1291 / 12800) ≤ (2294028061 / 1000000000) := by
  have h := checkLog_sound (w := (309 / 2891)) (n := 12)
    (lo := (214586517 / 1000000000)) (hi := (107293259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1291) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1291) = 1/(1291 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2294028061 / 1000000000) (-2294028057 / 1000000000) (Real.log (1291 / 12800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (33622881 / 50000000) ≤ -Real.log (500000 / 979523) ∧
    -Real.log (500000 / 979523) ≤ (672457621 / 1000000000) := by
  have h := checkLog_sound (w := (479523 / 1479523)) (n := 12)
    (lo := (33622881 / 50000000)) (hi := (672457621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((979523 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(979523 / 500000) = 1/(500000 / 979523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (33622881 / 50000000) (672457621 / 1000000000) (Real.log (979523 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (979523 / 500000) = -Real.log (500000 / 979523) := by
    rw [show ((979523 / 500000) : ℝ) = ((500000 / 979523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3195305791 / 1000000000) ≤ -Real.log (20477 / 500000) ∧
    -Real.log (20477 / 500000) ≤ (798826449 / 250000000) := by
  have h := checkLog_sound (w := (10773 / 51727)) (n := 12)
    (lo := (422717071 / 1000000000)) (hi := (26419817 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20477) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 20477) = 1/(20477 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-798826449 / 250000000) (-3195305791 / 1000000000) (Real.log (20477 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (1313957 / 1953125) ≤ -Real.log (1000000 / 1959611) ∧
    -Real.log (1000000 / 1959611) ≤ (134549197 / 200000000) := by
  have h := checkLog_sound (w := (959611 / 2959611)) (n := 12)
    (lo := (1313957 / 1953125)) (hi := (134549197 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1959611 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1959611 / 1000000) = 1/(1000000 / 1959611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (1313957 / 1953125) (134549197 / 200000000) (Real.log (1959611 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1959611 / 1000000) = -Real.log (1000000 / 1959611) := by
    rw [show ((1959611 / 1000000) : ℝ) = ((1000000 / 1959611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1604598903 / 500000000) ≤ -Real.log (40389 / 1000000) ∧
    -Real.log (40389 / 1000000) ≤ (3209197811 / 1000000000) := by
  have h := checkLog_sound (w := (22111 / 102889)) (n := 12)
    (lo := (218304543 / 500000000)) (hi := (436609087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 40389) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 40389) = 1/(40389 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3209197811 / 1000000000) (-1604598903 / 500000000) (Real.log (40389 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (672207467 / 1000000000) ≤ -Real.log (250000 / 489639) ∧
    -Real.log (250000 / 489639) ≤ (168051867 / 250000000) := by
  have h := checkLog_sound (w := (239639 / 739639)) (n := 12)
    (lo := (672207467 / 1000000000)) (hi := (168051867 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((489639 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(489639 / 250000) = 1/(250000 / 489639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (672207467 / 1000000000) (168051867 / 250000000) (Real.log (489639 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (489639 / 250000) = -Real.log (250000 / 489639) := by
    rw [show ((489639 / 250000) : ℝ) = ((250000 / 489639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1591706079 / 500000000) ≤ -Real.log (10361 / 250000) ∧
    -Real.log (10361 / 250000) ≤ (3183412163 / 1000000000) := by
  have h := checkLog_sound (w := (2632 / 12993)) (n := 12)
    (lo := (205411719 / 500000000)) (hi := (410823439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 10361) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 10361) = 1/(10361 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3183412163 / 1000000000) (-1591706079 / 500000000) (Real.log (10361 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (67250407 / 100000000) ≤ -Real.log (1000000 / 1959137) ∧
    -Real.log (1000000 / 1959137) ≤ (672504071 / 1000000000) := by
  have h := checkLog_sound (w := (959137 / 2959137)) (n := 12)
    (lo := (67250407 / 100000000)) (hi := (672504071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1959137 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1959137 / 1000000) = 1/(1000000 / 1959137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (67250407 / 100000000) (672504071 / 1000000000) (Real.log (1959137 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1959137 / 1000000) = -Real.log (1000000 / 1959137) := by
    rw [show ((1959137 / 1000000) : ℝ) = ((1000000 / 1959137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (799382567 / 250000000) ≤ -Real.log (40863 / 1000000) ∧
    -Real.log (40863 / 1000000) ≤ (3197530273 / 1000000000) := by
  have h := checkLog_sound (w := (21637 / 103363)) (n := 12)
    (lo := (106235387 / 250000000)) (hi := (424941549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 40863) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 40863) = 1/(40863 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3197530273 / 1000000000) (-799382567 / 250000000) (Real.log (40863 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (386776341 / 100000000) ≤ -Real.log (62500000000 / 2989704912829) ∧
    -Real.log (62500000000 / 2989704912829) ≤ (483470427 / 125000000) := by
  have h := checkLog_sound (w := (989704912829 / 4989704912829)) (n := 12)
    (lo := (40202751 / 100000000)) (hi := (402027511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2989704912829 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(2989704912829 / 2000000000000) = 1/(62500000000 / 2989704912829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (386776341 / 100000000) (483470427 / 125000000) (Real.log (2989704912829 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2989704912829 / 62500000000) = -Real.log (62500000000 / 2989704912829) := by
    rw [show ((2989704912829 / 62500000000) : ℝ) = ((62500000000 / 2989704912829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3881943789 / 1000000000) ≤ -Real.log (500000000000 / 24259216618387) ∧
    -Real.log (500000000000 / 24259216618387) ≤ (776388759 / 200000000) := by
  have h := checkLog_sound (w := (8259216618387 / 40259216618387)) (n := 12)
    (lo := (416207889 / 1000000000)) (hi := (41620789 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24259216618387 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(24259216618387 / 16000000000000) = 1/(500000000000 / 24259216618387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3881943789 / 1000000000) (776388759 / 200000000) (Real.log (24259216618387 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (24259216618387 / 500000000000) = -Real.log (500000000000 / 24259216618387) := by
    rw [show ((24259216618387 / 500000000000) : ℝ) = ((500000000000 / 24259216618387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (481952453 / 125000000) ≤ -Real.log (12500000000 / 590723627063) ∧
    -Real.log (12500000000 / 590723627063) ≤ (385561963 / 100000000) := by
  have h := checkLog_sound (w := (190723627063 / 990723627063)) (n := 12)
    (lo := (97470931 / 250000000)) (hi := (15595349 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590723627063 / 400000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(590723627063 / 400000000000) = 1/(12500000000 / 590723627063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (481952453 / 125000000) (385561963 / 100000000) (Real.log (590723627063 / 12500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (590723627063 / 12500000000) = -Real.log (12500000000 / 590723627063) := by
    rw [show ((590723627063 / 12500000000) : ℝ) = ((12500000000 / 590723627063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1935017169 / 500000000) ≤ -Real.log (500000000000 / 23972016249419) ∧
    -Real.log (500000000000 / 23972016249419) ≤ (483754293 / 125000000) := by
  have h := checkLog_sound (w := (7972016249419 / 39972016249419)) (n := 12)
    (lo := (202149219 / 500000000)) (hi := (404298439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23972016249419 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(23972016249419 / 16000000000000) = 1/(500000000000 / 23972016249419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1935017169 / 500000000) (483754293 / 125000000) (Real.log (23972016249419 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (23972016249419 / 500000000000) = -Real.log (500000000000 / 23972016249419) := by
    rw [show ((23972016249419 / 500000000000) : ℝ) = ((500000000000 / 23972016249419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0115
