import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0457
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

theorem reflection_log_1_neg : (93231679 / 500000000) ≤ -Real.log (10240 / 12339) ∧
    -Real.log (10240 / 12339) ≤ (186463359 / 1000000000) := by
  have h := checkLog_sound (w := (2099 / 22579)) (n := 12)
    (lo := (93231679 / 500000000)) (hi := (186463359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12339 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12339 / 10240) = 1/(10240 / 12339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (93231679 / 500000000) (186463359 / 1000000000) (Real.log (12339 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12339 / 10240) = -Real.log (10240 / 12339) := by
    rw [show ((12339 / 10240) : ℝ) = ((10240 / 12339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (229388597 / 1000000000) ≤ -Real.log (8141 / 10240) ∧
    -Real.log (8141 / 10240) ≤ (114694299 / 500000000) := by
  have h := checkLog_sound (w := (2099 / 18381)) (n := 12)
    (lo := (229388597 / 1000000000)) (hi := (114694299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8141) = 1/(8141 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-114694299 / 500000000) (-229388597 / 1000000000) (Real.log (8141 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (186220197 / 1000000000) ≤ -Real.log (640 / 771) ∧
    -Real.log (640 / 771) ≤ (93110099 / 500000000) := by
  have h := checkLog_sound (w := (131 / 1411)) (n := 12)
    (lo := (186220197 / 1000000000)) (hi := (93110099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((771 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(771 / 640) = 1/(640 / 771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (186220197 / 1000000000) (93110099 / 500000000) (Real.log (771 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (771 / 640) = -Real.log (640 / 771) := by
    rw [show ((771 / 640) : ℝ) = ((640 / 771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (229020159 / 1000000000) ≤ -Real.log (509 / 640) ∧
    -Real.log (509 / 640) ≤ (89461 / 390625) := by
  have h := checkLog_sound (w := (131 / 1149)) (n := 12)
    (lo := (229020159 / 1000000000)) (hi := (89461 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 509) = 1/(509 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-89461 / 390625) (-229020159 / 1000000000) (Real.log (509 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (171781 / 500000) ≤ -Real.log (5120 / 7219) ∧
    -Real.log (5120 / 7219) ≤ (343562001 / 1000000000) := by
  have h := checkLog_sound (w := (2099 / 12339)) (n := 12)
    (lo := (171781 / 500000)) (hi := (343562001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7219 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7219 / 5120) = 1/(5120 / 7219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (171781 / 500000) (343562001 / 1000000000) (Real.log (7219 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7219 / 5120) = -Real.log (5120 / 7219) := by
    rw [show ((7219 / 5120) : ℝ) = ((5120 / 7219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (65945817 / 125000000) ≤ -Real.log (3021 / 5120) ∧
    -Real.log (3021 / 5120) ≤ (527566537 / 1000000000) := by
  have h := checkLog_sound (w := (2099 / 8141)) (n := 12)
    (lo := (65945817 / 125000000)) (hi := (527566537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3021) = 1/(3021 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-527566537 / 1000000000) (-65945817 / 125000000) (Real.log (3021 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (343146343 / 1000000000) ≤ -Real.log (320 / 451) ∧
    -Real.log (320 / 451) ≤ (42893293 / 125000000) := by
  have h := checkLog_sound (w := (131 / 771)) (n := 12)
    (lo := (343146343 / 1000000000)) (hi := (42893293 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((451 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(451 / 320) = 1/(320 / 451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (343146343 / 1000000000) (42893293 / 125000000) (Real.log (451 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (451 / 320) = -Real.log (320 / 451) := by
    rw [show ((451 / 320) : ℝ) = ((320 / 451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (26328699 / 50000000) ≤ -Real.log (189 / 320) ∧
    -Real.log (189 / 320) ≤ (526573981 / 1000000000) := by
  have h := checkLog_sound (w := (131 / 509)) (n := 12)
    (lo := (26328699 / 50000000)) (hi := (526573981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 189) = 1/(189 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-526573981 / 1000000000) (-26328699 / 50000000) (Real.log (189 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (63979537 / 250000000) ≤ -Real.log (1000000 / 1291647) ∧
    -Real.log (1000000 / 1291647) ≤ (255918149 / 1000000000) := by
  have h := checkLog_sound (w := (291647 / 2291647)) (n := 12)
    (lo := (63979537 / 250000000)) (hi := (255918149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1291647 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1291647 / 1000000) = 1/(1000000 / 1291647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (63979537 / 250000000) (255918149 / 1000000000) (Real.log (1291647 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1291647 / 1000000) = -Real.log (1000000 / 1291647) := by
    rw [show ((1291647 / 1000000) : ℝ) = ((1000000 / 1291647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (344812721 / 1000000000) ≤ -Real.log (708353 / 1000000) ∧
    -Real.log (708353 / 1000000) ≤ (172406361 / 500000000) := by
  have h := checkLog_sound (w := (291647 / 1708353)) (n := 12)
    (lo := (344812721 / 1000000000)) (hi := (172406361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 708353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 708353) = 1/(708353 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-172406361 / 500000000) (-344812721 / 1000000000) (Real.log (708353 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (256247131 / 1000000000) ≤ -Real.log (125000 / 161509) ∧
    -Real.log (125000 / 161509) ≤ (64061783 / 250000000) := by
  have h := checkLog_sound (w := (36509 / 286509)) (n := 12)
    (lo := (256247131 / 1000000000)) (hi := (64061783 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161509 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161509 / 125000) = 1/(125000 / 161509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (256247131 / 1000000000) (64061783 / 250000000) (Real.log (161509 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (161509 / 125000) = -Real.log (125000 / 161509) := by
    rw [show ((161509 / 125000) : ℝ) = ((125000 / 161509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (69082577 / 200000000) ≤ -Real.log (88491 / 125000) ∧
    -Real.log (88491 / 125000) ≤ (172706443 / 500000000) := by
  have h := checkLog_sound (w := (36509 / 213491)) (n := 12)
    (lo := (69082577 / 200000000)) (hi := (172706443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 88491) = 1/(88491 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-172706443 / 500000000) (-69082577 / 200000000) (Real.log (88491 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (191611603 / 1000000000) ≤ -Real.log (625 / 757) ∧
    -Real.log (625 / 757) ≤ (47902901 / 250000000) := by
  have h := checkLog_sound (w := (66 / 691)) (n := 12)
    (lo := (191611603 / 1000000000)) (hi := (47902901 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((757 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(757 / 625) = 1/(625 / 757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (191611603 / 1000000000) (47902901 / 250000000) (Real.log (757 / 625)) := by
  have h := reflection_log_13_neg
  have he : Real.log (757 / 625) = -Real.log (625 / 757) := by
    rw [show ((757 / 625) : ℝ) = ((625 / 757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (9489699 / 40000000) ≤ -Real.log (493 / 625) ∧
    -Real.log (493 / 625) ≤ (59310619 / 250000000) := by
  have h := checkLog_sound (w := (66 / 559)) (n := 12)
    (lo := (9489699 / 40000000)) (hi := (59310619 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 493) = 1/(493 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-59310619 / 250000000) (-9489699 / 40000000) (Real.log (493 / 625)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (38375649 / 200000000) ≤ -Real.log (1000000 / 1211523) ∧
    -Real.log (1000000 / 1211523) ≤ (95939123 / 500000000) := by
  have h := checkLog_sound (w := (211523 / 2211523)) (n := 12)
    (lo := (38375649 / 200000000)) (hi := (95939123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1211523 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1211523 / 1000000) = 1/(1000000 / 1211523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (38375649 / 200000000) (95939123 / 500000000) (Real.log (1211523 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1211523 / 1000000) = -Real.log (1000000 / 1211523) := by
    rw [show ((1211523 / 1000000) : ℝ) = ((1000000 / 1211523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (118826021 / 500000000) ≤ -Real.log (788477 / 1000000) ∧
    -Real.log (788477 / 1000000) ≤ (237652043 / 1000000000) := by
  have h := checkLog_sound (w := (211523 / 1788477)) (n := 12)
    (lo := (118826021 / 500000000)) (hi := (237652043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 788477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 788477) = 1/(788477 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-237652043 / 1000000000) (-118826021 / 500000000) (Real.log (788477 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (60073087 / 100000000) ≤ -Real.log (250000000000 / 455862754869) ∧
    -Real.log (250000000000 / 455862754869) ≤ (600730871 / 1000000000) := by
  have h := checkLog_sound (w := (205862754869 / 705862754869)) (n := 12)
    (lo := (60073087 / 100000000)) (hi := (600730871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((455862754869 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(455862754869 / 250000000000) = 1/(250000000000 / 455862754869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (60073087 / 100000000) (600730871 / 1000000000) (Real.log (455862754869 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (455862754869 / 250000000000) = -Real.log (250000000000 / 455862754869) := by
    rw [show ((455862754869 / 250000000000) : ℝ) = ((250000000000 / 455862754869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (37603751 / 62500000) ≤ -Real.log (250000000000 / 456286515013) ∧
    -Real.log (250000000000 / 456286515013) ≤ (601660017 / 1000000000) := by
  have h := checkLog_sound (w := (206286515013 / 706286515013)) (n := 12)
    (lo := (37603751 / 62500000)) (hi := (601660017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((456286515013 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(456286515013 / 250000000000) = 1/(250000000000 / 456286515013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (37603751 / 62500000) (601660017 / 1000000000) (Real.log (456286515013 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (456286515013 / 250000000000) = -Real.log (250000000000 / 456286515013) := by
    rw [show ((456286515013 / 250000000000) : ℝ) = ((250000000000 / 456286515013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (428854079 / 1000000000) ≤ -Real.log (500000000000 / 767748478701) ∧
    -Real.log (500000000000 / 767748478701) ≤ (1340169 / 3125000) := by
  have h := checkLog_sound (w := (267748478701 / 1267748478701)) (n := 12)
    (lo := (428854079 / 1000000000)) (hi := (1340169 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((767748478701 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(767748478701 / 500000000000) = 1/(500000000000 / 767748478701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (428854079 / 1000000000) (1340169 / 3125000) (Real.log (767748478701 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (767748478701 / 500000000000) = -Real.log (500000000000 / 767748478701) := by
    rw [show ((767748478701 / 500000000000) : ℝ) = ((500000000000 / 767748478701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (26845643 / 62500000) ≤ -Real.log (100000000000 / 153653562501) ∧
    -Real.log (100000000000 / 153653562501) ≤ (429530289 / 1000000000) := by
  have h := checkLog_sound (w := (53653562501 / 253653562501)) (n := 12)
    (lo := (26845643 / 62500000)) (hi := (429530289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153653562501 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153653562501 / 100000000000) = 1/(100000000000 / 153653562501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (26845643 / 62500000) (429530289 / 1000000000) (Real.log (153653562501 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (153653562501 / 100000000000) = -Real.log (100000000000 / 153653562501) := by
    rw [show ((153653562501 / 100000000000) : ℝ) = ((100000000000 / 153653562501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0457
