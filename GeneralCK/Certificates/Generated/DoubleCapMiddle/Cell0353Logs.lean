import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0353
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

theorem reflection_log_1_neg : (211434643 / 1000000000) ≤ -Real.log (10240 / 12651) ∧
    -Real.log (10240 / 12651) ≤ (52858661 / 250000000) := by
  have h := checkLog_sound (w := (2411 / 22891)) (n := 12)
    (lo := (211434643 / 1000000000)) (hi := (52858661 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12651 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12651 / 10240) = 1/(10240 / 12651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (211434643 / 1000000000) (52858661 / 250000000) (Real.log (12651 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12651 / 10240) = -Real.log (10240 / 12651) := by
    rw [show ((12651 / 10240) : ℝ) = ((10240 / 12651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (268466831 / 1000000000) ≤ -Real.log (7829 / 10240) ∧
    -Real.log (7829 / 10240) ≤ (16779177 / 62500000) := by
  have h := checkLog_sound (w := (2411 / 18069)) (n := 12)
    (lo := (268466831 / 1000000000)) (hi := (16779177 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7829) = 1/(7829 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-16779177 / 62500000) (-268466831 / 1000000000) (Real.log (7829 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (5279937 / 25000000) ≤ -Real.log (1280 / 1581) ∧
    -Real.log (1280 / 1581) ≤ (211197481 / 1000000000) := by
  have h := checkLog_sound (w := (301 / 2861)) (n := 12)
    (lo := (5279937 / 25000000)) (hi := (211197481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1581 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1581 / 1280) = 1/(1280 / 1581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (5279937 / 25000000) (211197481 / 1000000000) (Real.log (1581 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1581 / 1280) = -Real.log (1280 / 1581) := by
    rw [show ((1581 / 1280) : ℝ) = ((1280 / 1581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (134041857 / 500000000) ≤ -Real.log (979 / 1280) ∧
    -Real.log (979 / 1280) ≤ (53616743 / 200000000) := by
  have h := checkLog_sound (w := (301 / 2259)) (n := 12)
    (lo := (134041857 / 500000000)) (hi := (53616743 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 979) = 1/(979 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-53616743 / 200000000) (-134041857 / 500000000) (Real.log (979 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (96468349 / 250000000) ≤ -Real.log (5120 / 7531) ∧
    -Real.log (5120 / 7531) ≤ (385873397 / 1000000000) := by
  have h := checkLog_sound (w := (2411 / 12651)) (n := 12)
    (lo := (96468349 / 250000000)) (hi := (385873397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7531 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7531 / 5120) = 1/(5120 / 7531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (96468349 / 250000000) (385873397 / 1000000000) (Real.log (7531 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7531 / 5120) = -Real.log (5120 / 7531) := by
    rw [show ((7531 / 5120) : ℝ) = ((5120 / 7531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (5092599 / 8000000) ≤ -Real.log (2709 / 5120) ∧
    -Real.log (2709 / 5120) ≤ (159143719 / 250000000) := by
  have h := checkLog_sound (w := (2411 / 7829)) (n := 12)
    (lo := (5092599 / 8000000)) (hi := (159143719 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2709) = 1/(2709 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-159143719 / 250000000) (-5092599 / 8000000) (Real.log (2709 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (385474963 / 1000000000) ≤ -Real.log (640 / 941) ∧
    -Real.log (640 / 941) ≤ (96368741 / 250000000) := by
  have h := checkLog_sound (w := (301 / 1581)) (n := 12)
    (lo := (385474963 / 1000000000)) (hi := (96368741 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((941 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(941 / 640) = 1/(640 / 941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (385474963 / 1000000000) (96368741 / 250000000) (Real.log (941 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (941 / 640) = -Real.log (640 / 941) := by
    rw [show ((941 / 640) : ℝ) = ((640 / 941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (158867017 / 250000000) ≤ -Real.log (339 / 640) ∧
    -Real.log (339 / 640) ≤ (635468069 / 1000000000) := by
  have h := checkLog_sound (w := (301 / 979)) (n := 12)
    (lo := (158867017 / 250000000)) (hi := (635468069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 339) = 1/(339 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-635468069 / 1000000000) (-158867017 / 250000000) (Real.log (339 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (144819453 / 500000000) ≤ -Real.log (200000 / 267189) ∧
    -Real.log (200000 / 267189) ≤ (289638907 / 1000000000) := by
  have h := checkLog_sound (w := (67189 / 467189)) (n := 12)
    (lo := (144819453 / 500000000)) (hi := (289638907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((267189 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(267189 / 200000) = 1/(200000 / 267189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (144819453 / 500000000) (289638907 / 1000000000) (Real.log (267189 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (267189 / 200000) = -Real.log (200000 / 267189) := by
    rw [show ((267189 / 200000) : ℝ) = ((200000 / 267189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (409390301 / 1000000000) ≤ -Real.log (132811 / 200000) ∧
    -Real.log (132811 / 200000) ≤ (204695151 / 500000000) := by
  have h := checkLog_sound (w := (67189 / 332811)) (n := 12)
    (lo := (409390301 / 1000000000)) (hi := (204695151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 132811) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 132811) = 1/(132811 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-204695151 / 500000000) (-409390301 / 1000000000) (Real.log (132811 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (36244997 / 125000000) ≤ -Real.log (500000 / 668187) ∧
    -Real.log (500000 / 668187) ≤ (289959977 / 1000000000) := by
  have h := checkLog_sound (w := (168187 / 1168187)) (n := 12)
    (lo := (36244997 / 125000000)) (hi := (289959977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((668187 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(668187 / 500000) = 1/(500000 / 668187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (36244997 / 125000000) (289959977 / 1000000000) (Real.log (668187 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (668187 / 500000) = -Real.log (500000 / 668187) := by
    rw [show ((668187 / 500000) : ℝ) = ((500000 / 668187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (410036541 / 1000000000) ≤ -Real.log (331813 / 500000) ∧
    -Real.log (331813 / 500000) ≤ (205018271 / 500000000) := by
  have h := checkLog_sound (w := (168187 / 831813)) (n := 12)
    (lo := (410036541 / 1000000000)) (hi := (205018271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 331813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 331813) = 1/(331813 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-205018271 / 500000000) (-410036541 / 1000000000) (Real.log (331813 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (27412823 / 125000000) ≤ -Real.log (125000 / 155651) ∧
    -Real.log (125000 / 155651) ≤ (43860517 / 200000000) := by
  have h := checkLog_sound (w := (30651 / 280651)) (n := 12)
    (lo := (27412823 / 125000000)) (hi := (43860517 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155651 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155651 / 125000) = 1/(125000 / 155651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (27412823 / 125000000) (43860517 / 200000000) (Real.log (155651 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (155651 / 125000) = -Real.log (125000 / 155651) := by
    rw [show ((155651 / 125000) : ℝ) = ((125000 / 155651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (35164133 / 125000000) ≤ -Real.log (94349 / 125000) ∧
    -Real.log (94349 / 125000) ≤ (56262613 / 200000000) := by
  have h := checkLog_sound (w := (30651 / 219349)) (n := 12)
    (lo := (35164133 / 125000000)) (hi := (56262613 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 94349) = 1/(94349 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-56262613 / 200000000) (-35164133 / 125000000) (Real.log (94349 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (219569973 / 1000000000) ≤ -Real.log (1000000 / 1245541) ∧
    -Real.log (1000000 / 1245541) ≤ (109784987 / 500000000) := by
  have h := checkLog_sound (w := (245541 / 2245541)) (n := 12)
    (lo := (219569973 / 1000000000)) (hi := (109784987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1245541 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1245541 / 1000000) = 1/(1000000 / 1245541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (219569973 / 1000000000) (109784987 / 500000000) (Real.log (1245541 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1245541 / 1000000) = -Real.log (1000000 / 1245541) := by
    rw [show ((1245541 / 1000000) : ℝ) = ((1000000 / 1245541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (140877171 / 500000000) ≤ -Real.log (754459 / 1000000) ∧
    -Real.log (754459 / 1000000) ≤ (281754343 / 1000000000) := by
  have h := checkLog_sound (w := (245541 / 1754459)) (n := 12)
    (lo := (140877171 / 500000000)) (hi := (281754343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 754459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 754459) = 1/(754459 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-281754343 / 1000000000) (-140877171 / 500000000) (Real.log (754459 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (699029207 / 1000000000) ≤ -Real.log (100000000000 / 201179872149) ∧
    -Real.log (100000000000 / 201179872149) ≤ (699029209 / 1000000000) := by
  have h := checkLog_sound (w := (1179872149 / 401179872149)) (n := 12)
    (lo := (5882027 / 1000000000)) (hi := (1470507 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201179872149 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(201179872149 / 200000000000) = 1/(100000000000 / 201179872149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (699029207 / 1000000000) (699029209 / 1000000000) (Real.log (201179872149 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (201179872149 / 100000000000) = -Real.log (100000000000 / 201179872149) := by
    rw [show ((201179872149 / 100000000000) : ℝ) = ((100000000000 / 201179872149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (174999129 / 250000000) ≤ -Real.log (31250000000 / 62929552941) ∧
    -Real.log (31250000000 / 62929552941) ≤ (349998259 / 500000000) := by
  have h := checkLog_sound (w := (429552941 / 125429552941)) (n := 12)
    (lo := (856167 / 125000000)) (hi := (6849337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62929552941 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62929552941 / 62500000000) = 1/(31250000000 / 62929552941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (174999129 / 250000000) (349998259 / 500000000) (Real.log (62929552941 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (62929552941 / 31250000000) = -Real.log (31250000000 / 62929552941) := by
    rw [show ((62929552941 / 31250000000) : ℝ) = ((31250000000 / 62929552941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (15644239 / 31250000) ≤ -Real.log (50000000000 / 82486830809) ∧
    -Real.log (50000000000 / 82486830809) ≤ (500615649 / 1000000000) := by
  have h := checkLog_sound (w := (32486830809 / 132486830809)) (n := 12)
    (lo := (15644239 / 31250000)) (hi := (500615649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82486830809 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82486830809 / 50000000000) = 1/(50000000000 / 82486830809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (15644239 / 31250000) (500615649 / 1000000000) (Real.log (82486830809 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (82486830809 / 50000000000) = -Real.log (50000000000 / 82486830809) := by
    rw [show ((82486830809 / 50000000000) : ℝ) = ((50000000000 / 82486830809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (125331079 / 250000000) ≤ -Real.log (500000000000 / 825453072997) ∧
    -Real.log (500000000000 / 825453072997) ≤ (501324317 / 1000000000) := by
  have h := checkLog_sound (w := (325453072997 / 1325453072997)) (n := 12)
    (lo := (125331079 / 250000000)) (hi := (501324317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((825453072997 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(825453072997 / 500000000000) = 1/(500000000000 / 825453072997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (125331079 / 250000000) (501324317 / 1000000000) (Real.log (825453072997 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (825453072997 / 500000000000) = -Real.log (500000000000 / 825453072997) := by
    rw [show ((825453072997 / 500000000000) : ℝ) = ((500000000000 / 825453072997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0353
