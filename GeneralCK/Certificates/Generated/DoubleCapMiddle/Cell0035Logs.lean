import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0035
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

theorem reflection_log_1_neg : (193268549 / 500000000) ≤ -Real.log (320 / 471) ∧
    -Real.log (320 / 471) ≤ (386537099 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 791)) (n := 12)
    (lo := (193268549 / 500000000)) (hi := (386537099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((471 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(471 / 320) = 1/(320 / 471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (193268549 / 500000000) (386537099 / 1000000000) (Real.log (471 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (471 / 320) = -Real.log (320 / 471) := by
    rw [show ((471 / 320) : ℝ) = ((320 / 471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (15960557 / 25000000) ≤ -Real.log (169 / 320) ∧
    -Real.log (169 / 320) ≤ (638422281 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 489)) (n := 12)
    (lo := (15960557 / 25000000)) (hi := (638422281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 169) = 1/(169 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-638422281 / 1000000000) (-15960557 / 25000000) (Real.log (169 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (192870301 / 500000000) ≤ -Real.log (512 / 753) ∧
    -Real.log (512 / 753) ≤ (385740603 / 1000000000) := by
  have h := checkLog_sound (w := (241 / 1265)) (n := 12)
    (lo := (192870301 / 500000000)) (hi := (385740603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((753 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(753 / 512) = 1/(512 / 753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (192870301 / 500000000) (385740603 / 1000000000) (Real.log (753 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (753 / 512) = -Real.log (512 / 753) := by
    rw [show ((753 / 512) : ℝ) = ((512 / 753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (159051451 / 250000000) ≤ -Real.log (271 / 512) ∧
    -Real.log (271 / 512) ≤ (127241161 / 200000000) := by
  have h := checkLog_sound (w := (241 / 783)) (n := 12)
    (lo := (159051451 / 250000000)) (hi := (127241161 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 271) = 1/(271 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-127241161 / 200000000) (-159051451 / 250000000) (Real.log (271 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (83077387 / 125000000) ≤ -Real.log (160 / 311) ∧
    -Real.log (160 / 311) ≤ (664619097 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 471)) (n := 12)
    (lo := (83077387 / 125000000)) (hi := (664619097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311 / 160) = 1/(160 / 311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (83077387 / 125000000) (664619097 / 1000000000) (Real.log (311 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (311 / 160) = -Real.log (160 / 311) := by
    rw [show ((311 / 160) : ℝ) = ((160 / 311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (575589847 / 200000000) ≤ -Real.log (9 / 160) ∧
    -Real.log (9 / 160) ≤ (71948731 / 25000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(10 / 9) = 1/(9 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-71948731 / 25000000) (-575589847 / 200000000) (Real.log (9 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (663412581 / 1000000000) ≤ -Real.log (256 / 497) ∧
    -Real.log (256 / 497) ≤ (331706291 / 500000000) := by
  have h := checkLog_sound (w := (241 / 753)) (n := 12)
    (lo := (663412581 / 1000000000)) (hi := (331706291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((497 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(497 / 256) = 1/(256 / 497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (663412581 / 1000000000) (331706291 / 500000000) (Real.log (497 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (497 / 256) = -Real.log (256 / 497) := by
    rw [show ((497 / 256) : ℝ) = ((256 / 497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2837127241 / 1000000000) ≤ -Real.log (15 / 256) ∧
    -Real.log (15 / 256) ≤ (1418563623 / 500000000) := by
  have h := checkLog_sound (w := (1 / 31)) (n := 12)
    (lo := (64538521 / 1000000000)) (hi := (32269261 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 15) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(16 / 15) = 1/(15 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1418563623 / 500000000) (-2837127241 / 1000000000) (Real.log (15 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (537294803 / 1000000000) ≤ -Real.log (1000000 / 1711371) ∧
    -Real.log (1000000 / 1711371) ≤ (134323701 / 250000000) := by
  have h := checkLog_sound (w := (711371 / 2711371)) (n := 12)
    (lo := (537294803 / 1000000000)) (hi := (134323701 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1711371 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1711371 / 1000000) = 1/(1000000 / 1711371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (537294803 / 1000000000) (134323701 / 250000000) (Real.log (1711371 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1711371 / 1000000) = -Real.log (1000000 / 1711371) := by
    rw [show ((1711371 / 1000000) : ℝ) = ((1000000 / 1711371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (38831661 / 31250000) ≤ -Real.log (288629 / 1000000) ∧
    -Real.log (288629 / 1000000) ≤ (621306577 / 500000000) := by
  have h := checkLog_sound (w := (211371 / 788629)) (n := 12)
    (lo := (137366493 / 250000000)) (hi := (549465973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 288629) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 288629) = 1/(288629 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-621306577 / 500000000) (-38831661 / 31250000) (Real.log (288629 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (269323011 / 500000000) ≤ -Real.log (200000 / 342737) ∧
    -Real.log (200000 / 342737) ≤ (538646023 / 1000000000) := by
  have h := checkLog_sound (w := (142737 / 542737)) (n := 12)
    (lo := (269323011 / 500000000)) (hi := (538646023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342737 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342737 / 200000) = 1/(200000 / 342737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (269323011 / 500000000) (538646023 / 1000000000) (Real.log (342737 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (342737 / 200000) = -Real.log (200000 / 342737) := by
    rw [show ((342737 / 200000) : ℝ) = ((200000 / 342737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (50026507 / 40000000) ≤ -Real.log (57263 / 200000) ∧
    -Real.log (57263 / 200000) ≤ (1250662677 / 1000000000) := by
  have h := checkLog_sound (w := (42737 / 157263)) (n := 12)
    (lo := (111503099 / 200000000)) (hi := (69689437 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 57263) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 57263) = 1/(57263 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1250662677 / 1000000000) (-50026507 / 40000000) (Real.log (57263 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (57455093 / 125000000) ≤ -Real.log (200000 / 316701) ∧
    -Real.log (200000 / 316701) ≤ (91928149 / 200000000) := by
  have h := checkLog_sound (w := (116701 / 516701)) (n := 12)
    (lo := (57455093 / 125000000)) (hi := (91928149 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((316701 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(316701 / 200000) = 1/(200000 / 316701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (57455093 / 125000000) (91928149 / 200000000) (Real.log (316701 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (316701 / 200000) = -Real.log (200000 / 316701) := by
    rw [show ((316701 / 200000) : ℝ) = ((200000 / 316701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (875880821 / 1000000000) ≤ -Real.log (83299 / 200000) ∧
    -Real.log (83299 / 200000) ≤ (875880823 / 1000000000) := by
  have h := checkLog_sound (w := (16701 / 183299)) (n := 12)
    (lo := (182733641 / 1000000000)) (hi := (91366821 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 83299) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 83299) = 1/(83299 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-875880823 / 1000000000) (-875880821 / 1000000000) (Real.log (83299 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (115301889 / 250000000) ≤ -Real.log (250000 / 396497) ∧
    -Real.log (250000 / 396497) ≤ (461207557 / 1000000000) := by
  have h := checkLog_sound (w := (146497 / 646497)) (n := 12)
    (lo := (115301889 / 250000000)) (hi := (461207557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((396497 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(396497 / 250000) = 1/(250000 / 396497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (115301889 / 250000000) (461207557 / 1000000000) (Real.log (396497 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (396497 / 250000) = -Real.log (250000 / 396497) := by
    rw [show ((396497 / 250000) : ℝ) = ((250000 / 396497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (881860319 / 1000000000) ≤ -Real.log (103503 / 250000) ∧
    -Real.log (103503 / 250000) ≤ (881860321 / 1000000000) := by
  have h := checkLog_sound (w := (21497 / 228503)) (n := 12)
    (lo := (188713139 / 1000000000)) (hi := (9435657 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 103503) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 103503) = 1/(103503 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-881860321 / 1000000000) (-881860319 / 1000000000) (Real.log (103503 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (355981591 / 200000000) ≤ -Real.log (100000000000 / 592931063753) ∧
    -Real.log (100000000000 / 592931063753) ≤ (889953979 / 500000000) := by
  have h := checkLog_sound (w := (192931063753 / 992931063753)) (n := 12)
    (lo := (78722719 / 200000000)) (hi := (98403399 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592931063753 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(592931063753 / 400000000000) = 1/(100000000000 / 592931063753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (355981591 / 200000000) (889953979 / 500000000) (Real.log (592931063753 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (592931063753 / 100000000000) = -Real.log (100000000000 / 592931063753) := by
    rw [show ((592931063753 / 100000000000) : ℝ) = ((100000000000 / 592931063753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1789308697 / 1000000000) ≤ -Real.log (500000000000 / 2992656689311) ∧
    -Real.log (500000000000 / 2992656689311) ≤ (17893087 / 10000000) := by
  have h := checkLog_sound (w := (992656689311 / 4992656689311)) (n := 12)
    (lo := (403014337 / 1000000000)) (hi := (201507169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2992656689311 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2992656689311 / 2000000000000) = 1/(500000000000 / 2992656689311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1789308697 / 1000000000) (17893087 / 10000000) (Real.log (2992656689311 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2992656689311 / 500000000000) = -Real.log (500000000000 / 2992656689311) := by
    rw [show ((2992656689311 / 500000000000) : ℝ) = ((500000000000 / 2992656689311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (667760783 / 500000000) ≤ -Real.log (500000000000 / 1900989207553) ∧
    -Real.log (500000000000 / 1900989207553) ≤ (41735049 / 31250000) := by
  have h := checkLog_sound (w := (900989207553 / 2900989207553)) (n := 12)
    (lo := (321187193 / 500000000)) (hi := (642374387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1900989207553 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1900989207553 / 1000000000000) = 1/(500000000000 / 1900989207553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (667760783 / 500000000) (41735049 / 31250000) (Real.log (1900989207553 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1900989207553 / 500000000000) = -Real.log (500000000000 / 1900989207553) := by
    rw [show ((1900989207553 / 500000000000) : ℝ) = ((500000000000 / 1900989207553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (335766969 / 250000000) ≤ -Real.log (20000000000 / 76615557037) ∧
    -Real.log (20000000000 / 76615557037) ≤ (671533939 / 500000000) := by
  have h := checkLog_sound (w := (36615557037 / 116615557037)) (n := 12)
    (lo := (81240087 / 125000000)) (hi := (649920697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76615557037 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(76615557037 / 40000000000) = 1/(20000000000 / 76615557037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (335766969 / 250000000) (671533939 / 500000000) (Real.log (76615557037 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (76615557037 / 20000000000) = -Real.log (20000000000 / 76615557037) := by
    rw [show ((76615557037 / 20000000000) : ℝ) = ((20000000000 / 76615557037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0035
