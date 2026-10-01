import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0055
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

theorem reflection_log_1_neg : (370485389 / 1000000000) ≤ -Real.log (640 / 927) ∧
    -Real.log (640 / 927) ≤ (37048539 / 100000000) := by
  have h := checkLog_sound (w := (287 / 1567)) (n := 12)
    (lo := (370485389 / 1000000000)) (hi := (37048539 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((927 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(927 / 640) = 1/(640 / 927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (370485389 / 1000000000) (37048539 / 100000000) (Real.log (927 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (927 / 640) = -Real.log (640 / 927) := by
    rw [show ((927 / 640) : ℝ) = ((640 / 927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (595000119 / 1000000000) ≤ -Real.log (353 / 640) ∧
    -Real.log (353 / 640) ≤ (14875003 / 25000000) := by
  have h := checkLog_sound (w := (287 / 993)) (n := 12)
    (lo := (595000119 / 1000000000)) (hi := (14875003 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 353) = 1/(353 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-14875003 / 25000000) (-595000119 / 1000000000) (Real.log (353 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (92419 / 250000) ≤ -Real.log (512 / 741) ∧
    -Real.log (512 / 741) ≤ (369676001 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 1253)) (n := 12)
    (lo := (92419 / 250000)) (hi := (369676001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741 / 512) = 1/(512 / 741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (92419 / 250000) (369676001 / 1000000000) (Real.log (741 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (741 / 512) = -Real.log (512 / 741) := by
    rw [show ((741 / 512) : ℝ) = ((512 / 741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (592877727 / 1000000000) ≤ -Real.log (283 / 512) ∧
    -Real.log (283 / 512) ≤ (18527429 / 31250000) := by
  have h := checkLog_sound (w := (229 / 795)) (n := 12)
    (lo := (592877727 / 1000000000)) (hi := (18527429 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 283) = 1/(283 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-18527429 / 31250000) (-592877727 / 1000000000) (Real.log (283 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (128041559 / 200000000) ≤ -Real.log (320 / 607) ∧
    -Real.log (320 / 607) ≤ (160051949 / 250000000) := by
  have h := checkLog_sound (w := (287 / 927)) (n := 12)
    (lo := (128041559 / 200000000)) (hi := (160051949 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607 / 320) = 1/(320 / 607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (128041559 / 200000000) (160051949 / 250000000) (Real.log (607 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (607 / 320) = -Real.log (320 / 607) := by
    rw [show ((607 / 320) : ℝ) = ((320 / 607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (283976679 / 125000000) ≤ -Real.log (33 / 320) ∧
    -Real.log (33 / 320) ≤ (567953359 / 250000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(40 / 33) = 1/(33 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-567953359 / 250000000) (-283976679 / 125000000) (Real.log (33 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (319485723 / 500000000) ≤ -Real.log (256 / 485) ∧
    -Real.log (256 / 485) ≤ (638971447 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 741)) (n := 12)
    (lo := (319485723 / 500000000)) (hi := (638971447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((485 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(485 / 256) = 1/(256 / 485) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (319485723 / 500000000) (638971447 / 1000000000) (Real.log (485 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (485 / 256) = -Real.log (256 / 485) := by
    rw [show ((485 / 256) : ℝ) = ((256 / 485) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (70291893 / 31250000) ≤ -Real.log (27 / 256) ∧
    -Real.log (27 / 256) ≤ (112467029 / 50000000) := by
  have h := checkLog_sound (w := (5 / 59)) (n := 12)
    (lo := (42474759 / 250000000)) (hi := (169899037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 27) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(32 / 27) = 1/(27 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-112467029 / 50000000) (-70291893 / 31250000) (Real.log (27 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (51137887 / 100000000) ≤ -Real.log (1000000 / 1667589) ∧
    -Real.log (1000000 / 1667589) ≤ (511378871 / 1000000000) := by
  have h := checkLog_sound (w := (667589 / 2667589)) (n := 12)
    (lo := (51137887 / 100000000)) (hi := (511378871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1667589 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1667589 / 1000000) = 1/(1000000 / 1667589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (51137887 / 100000000) (511378871 / 1000000000) (Real.log (1667589 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1667589 / 1000000) = -Real.log (1000000 / 1667589) := by
    rw [show ((1667589 / 1000000) : ℝ) = ((1000000 / 1667589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1101383123 / 1000000000) ≤ -Real.log (332411 / 1000000) ∧
    -Real.log (332411 / 1000000) ≤ (1762213 / 1600000) := by
  have h := checkLog_sound (w := (167589 / 832411)) (n := 12)
    (lo := (408235943 / 1000000000)) (hi := (51029493 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 332411) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 332411) = 1/(332411 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1762213 / 1600000) (-1101383123 / 1000000000) (Real.log (332411 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (256319589 / 500000000) ≤ -Real.log (250000 / 417423) ∧
    -Real.log (250000 / 417423) ≤ (512639179 / 1000000000) := by
  have h := checkLog_sound (w := (167423 / 667423)) (n := 12)
    (lo := (256319589 / 500000000)) (hi := (512639179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((417423 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(417423 / 250000) = 1/(250000 / 417423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (256319589 / 500000000) (512639179 / 1000000000) (Real.log (417423 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (417423 / 250000) = -Real.log (250000 / 417423) := by
    rw [show ((417423 / 250000) : ℝ) = ((250000 / 417423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (44309189 / 40000000) ≤ -Real.log (82577 / 250000) ∧
    -Real.log (82577 / 250000) ≤ (1107729727 / 1000000000) := by
  have h := checkLog_sound (w := (42423 / 207577)) (n := 12)
    (lo := (82916509 / 200000000)) (hi := (207291273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 82577) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 82577) = 1/(82577 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1107729727 / 1000000000) (-44309189 / 40000000) (Real.log (82577 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (430244221 / 1000000000) ≤ -Real.log (1000000 / 1537633) ∧
    -Real.log (1000000 / 1537633) ≤ (215122111 / 500000000) := by
  have h := checkLog_sound (w := (537633 / 2537633)) (n := 12)
    (lo := (430244221 / 1000000000)) (hi := (215122111 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1537633 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1537633 / 1000000) = 1/(1000000 / 1537633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (430244221 / 1000000000) (215122111 / 500000000) (Real.log (1537633 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1537633 / 1000000) = -Real.log (1000000 / 1537633) := by
    rw [show ((1537633 / 1000000) : ℝ) = ((1000000 / 1537633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (77139633 / 100000000) ≤ -Real.log (462367 / 1000000) ∧
    -Real.log (462367 / 1000000) ≤ (192849083 / 250000000) := by
  have h := checkLog_sound (w := (37633 / 962367)) (n := 12)
    (lo := (1564983 / 20000000)) (hi := (78249151 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 462367) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 462367) = 1/(462367 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-192849083 / 250000000) (-77139633 / 100000000) (Real.log (462367 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (53955593 / 125000000) ≤ -Real.log (250000 / 384947) ∧
    -Real.log (250000 / 384947) ≤ (86328949 / 200000000) := by
  have h := checkLog_sound (w := (134947 / 634947)) (n := 12)
    (lo := (53955593 / 125000000)) (hi := (86328949 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((384947 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(384947 / 250000) = 1/(250000 / 384947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (53955593 / 125000000) (86328949 / 200000000) (Real.log (384947 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (384947 / 250000) = -Real.log (250000 / 384947) := by
    rw [show ((384947 / 250000) : ℝ) = ((250000 / 384947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (31042721 / 40000000) ≤ -Real.log (115053 / 250000) ∧
    -Real.log (115053 / 250000) ≤ (776068027 / 1000000000) := by
  have h := checkLog_sound (w := (9947 / 240053)) (n := 12)
    (lo := (16584169 / 200000000)) (hi := (41460423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 115053) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 115053) = 1/(115053 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-776068027 / 1000000000) (-31042721 / 40000000) (Real.log (115053 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1612761993 / 1000000000) ≤ -Real.log (250000000000 / 1254162016299) ∧
    -Real.log (250000000000 / 1254162016299) ≤ (403190499 / 250000000) := by
  have h := checkLog_sound (w := (254162016299 / 2254162016299)) (n := 12)
    (lo := (226467633 / 1000000000)) (hi := (113233817 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1254162016299 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1254162016299 / 1000000000000) = 1/(250000000000 / 1254162016299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1612761993 / 1000000000) (403190499 / 250000000) (Real.log (1254162016299 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1254162016299 / 250000000000) = -Real.log (250000000000 / 1254162016299) := by
    rw [show ((1254162016299 / 250000000000) : ℝ) = ((250000000000 / 1254162016299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1620368903 / 1000000000) ≤ -Real.log (62500000000 / 315934673093) ∧
    -Real.log (62500000000 / 315934673093) ≤ (810184453 / 500000000) := by
  have h := checkLog_sound (w := (65934673093 / 565934673093)) (n := 12)
    (lo := (234074543 / 1000000000)) (hi := (14629659 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((315934673093 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(315934673093 / 250000000000) = 1/(62500000000 / 315934673093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1620368903 / 1000000000) (810184453 / 500000000) (Real.log (315934673093 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (315934673093 / 62500000000) = -Real.log (62500000000 / 315934673093) := by
    rw [show ((315934673093 / 62500000000) : ℝ) = ((62500000000 / 315934673093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1201640551 / 1000000000) ≤ -Real.log (500000000000 / 1662784108727) ∧
    -Real.log (500000000000 / 1662784108727) ≤ (1201640553 / 1000000000) := by
  have h := checkLog_sound (w := (662784108727 / 2662784108727)) (n := 12)
    (lo := (508493371 / 1000000000)) (hi := (127123343 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1662784108727 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1662784108727 / 1000000000000) = 1/(500000000000 / 1662784108727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1201640551 / 1000000000) (1201640553 / 1000000000) (Real.log (1662784108727 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1662784108727 / 500000000000) = -Real.log (500000000000 / 1662784108727) := by
    rw [show ((1662784108727 / 500000000000) : ℝ) = ((500000000000 / 1662784108727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (120771277 / 100000000) ≤ -Real.log (62500000000 / 209113951831) ∧
    -Real.log (62500000000 / 209113951831) ≤ (301928193 / 250000000) := by
  have h := checkLog_sound (w := (84113951831 / 334113951831)) (n := 12)
    (lo := (51456559 / 100000000)) (hi := (514565591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((209113951831 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(209113951831 / 125000000000) = 1/(62500000000 / 209113951831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (120771277 / 100000000) (301928193 / 250000000) (Real.log (209113951831 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (209113951831 / 62500000000) = -Real.log (62500000000 / 209113951831) := by
    rw [show ((209113951831 / 62500000000) : ℝ) = ((62500000000 / 209113951831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0055
