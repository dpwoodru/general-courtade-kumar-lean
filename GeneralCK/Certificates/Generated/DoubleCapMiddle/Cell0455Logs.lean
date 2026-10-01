import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0455
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

theorem reflection_log_1_neg : (186949503 / 1000000000) ≤ -Real.log (2048 / 2469) ∧
    -Real.log (2048 / 2469) ≤ (1460543 / 7812500) := by
  have h := checkLog_sound (w := (421 / 4517)) (n := 12)
    (lo := (186949503 / 1000000000)) (hi := (1460543 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2469 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2469 / 2048) = 1/(2048 / 2469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (186949503 / 1000000000) (1460543 / 7812500) (Real.log (2469 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2469 / 2048) = -Real.log (2048 / 2469) := by
    rw [show ((2469 / 2048) : ℝ) = ((2048 / 2469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (115062939 / 500000000) ≤ -Real.log (1627 / 2048) ∧
    -Real.log (1627 / 2048) ≤ (230125879 / 1000000000) := by
  have h := checkLog_sound (w := (421 / 3675)) (n := 12)
    (lo := (115062939 / 500000000)) (hi := (230125879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1627) = 1/(1627 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-230125879 / 1000000000) (-115062939 / 500000000) (Real.log (1627 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (9335323 / 50000000) ≤ -Real.log (5120 / 6171) ∧
    -Real.log (5120 / 6171) ≤ (186706461 / 1000000000) := by
  have h := checkLog_sound (w := (1051 / 11291)) (n := 12)
    (lo := (9335323 / 50000000)) (hi := (186706461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6171 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6171 / 5120) = 1/(5120 / 6171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (9335323 / 50000000) (186706461 / 1000000000) (Real.log (6171 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6171 / 5120) = -Real.log (5120 / 6171) := by
    rw [show ((6171 / 5120) : ℝ) = ((5120 / 6171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (22975717 / 100000000) ≤ -Real.log (4069 / 5120) ∧
    -Real.log (4069 / 5120) ≤ (229757171 / 1000000000) := by
  have h := checkLog_sound (w := (1051 / 9189)) (n := 12)
    (lo := (22975717 / 100000000)) (hi := (229757171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4069) = 1/(4069 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-229757171 / 1000000000) (-22975717 / 100000000) (Real.log (4069 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (172196397 / 500000000) ≤ -Real.log (1024 / 1445) ∧
    -Real.log (1024 / 1445) ≤ (68878559 / 200000000) := by
  have h := checkLog_sound (w := (421 / 2469)) (n := 12)
    (lo := (172196397 / 500000000)) (hi := (68878559 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1445 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1445 / 1024) = 1/(1024 / 1445) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (172196397 / 500000000) (68878559 / 200000000) (Real.log (1445 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1445 / 1024) = -Real.log (1024 / 1445) := by
    rw [show ((1445 / 1024) : ℝ) = ((1024 / 1445) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (33097163 / 62500000) ≤ -Real.log (603 / 1024) ∧
    -Real.log (603 / 1024) ≤ (529554609 / 1000000000) := by
  have h := checkLog_sound (w := (421 / 1627)) (n := 12)
    (lo := (33097163 / 62500000)) (hi := (529554609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 603) = 1/(603 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-529554609 / 1000000000) (-33097163 / 62500000) (Real.log (603 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (343977483 / 1000000000) ≤ -Real.log (2560 / 3611) ∧
    -Real.log (2560 / 3611) ≤ (85994371 / 250000000) := by
  have h := checkLog_sound (w := (1051 / 6171)) (n := 12)
    (lo := (343977483 / 1000000000)) (hi := (85994371 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3611 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3611 / 2560) = 1/(2560 / 3611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (343977483 / 1000000000) (85994371 / 250000000) (Real.log (3611 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3611 / 2560) = -Real.log (2560 / 3611) := by
    rw [show ((3611 / 2560) : ℝ) = ((2560 / 3611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (264280039 / 500000000) ≤ -Real.log (1509 / 2560) ∧
    -Real.log (1509 / 2560) ≤ (528560079 / 1000000000) := by
  have h := checkLog_sound (w := (1051 / 4069)) (n := 12)
    (lo := (264280039 / 500000000)) (hi := (528560079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1509) = 1/(1509 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-528560079 / 1000000000) (-264280039 / 500000000) (Real.log (1509 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (128287229 / 500000000) ≤ -Real.log (200000 / 258499) ∧
    -Real.log (200000 / 258499) ≤ (256574459 / 1000000000) := by
  have h := checkLog_sound (w := (58499 / 458499)) (n := 12)
    (lo := (128287229 / 500000000)) (hi := (256574459 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((258499 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(258499 / 200000) = 1/(200000 / 258499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (128287229 / 500000000) (256574459 / 1000000000) (Real.log (258499 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (258499 / 200000) = -Real.log (200000 / 258499) := by
    rw [show ((258499 / 200000) : ℝ) = ((200000 / 258499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (173005291 / 500000000) ≤ -Real.log (141501 / 200000) ∧
    -Real.log (141501 / 200000) ≤ (346010583 / 1000000000) := by
  have h := checkLog_sound (w := (58499 / 341501)) (n := 12)
    (lo := (173005291 / 500000000)) (hi := (346010583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 141501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 141501) = 1/(141501 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-346010583 / 1000000000) (-173005291 / 500000000) (Real.log (141501 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (256903999 / 1000000000) ≤ -Real.log (1000000 / 1292921) ∧
    -Real.log (1000000 / 1292921) ≤ (32113 / 125000) := by
  have h := checkLog_sound (w := (292921 / 2292921)) (n := 12)
    (lo := (256903999 / 1000000000)) (hi := (32113 / 125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1292921 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1292921 / 1000000) = 1/(1000000 / 1292921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (256903999 / 1000000000) (32113 / 125000) (Real.log (1292921 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1292921 / 1000000) = -Real.log (1000000 / 1292921) := by
    rw [show ((1292921 / 1000000) : ℝ) = ((1000000 / 1292921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (346612879 / 1000000000) ≤ -Real.log (707079 / 1000000) ∧
    -Real.log (707079 / 1000000) ≤ (4332661 / 12500000) := by
  have h := checkLog_sound (w := (292921 / 1707079)) (n := 12)
    (lo := (346612879 / 1000000000)) (hi := (4332661 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 707079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 707079) = 1/(707079 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-4332661 / 12500000) (-346612879 / 1000000000) (Real.log (707079 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (96071583 / 500000000) ≤ -Real.log (250000 / 302961) ∧
    -Real.log (250000 / 302961) ≤ (192143167 / 1000000000) := by
  have h := checkLog_sound (w := (52961 / 552961)) (n := 12)
    (lo := (96071583 / 500000000)) (hi := (192143167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302961 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302961 / 250000) = 1/(250000 / 302961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (96071583 / 500000000) (192143167 / 1000000000) (Real.log (302961 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (302961 / 250000) = -Real.log (250000 / 302961) := by
    rw [show ((302961 / 250000) : ℝ) = ((250000 / 302961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (238059239 / 1000000000) ≤ -Real.log (197039 / 250000) ∧
    -Real.log (197039 / 250000) ≤ (5951481 / 25000000) := by
  have h := checkLog_sound (w := (52961 / 447039)) (n := 12)
    (lo := (238059239 / 1000000000)) (hi := (5951481 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 197039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 197039) = 1/(197039 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-5951481 / 25000000) (-238059239 / 1000000000) (Real.log (197039 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (96204833 / 500000000) ≤ -Real.log (1000000 / 1212167) ∧
    -Real.log (1000000 / 1212167) ≤ (192409667 / 1000000000) := by
  have h := checkLog_sound (w := (212167 / 2212167)) (n := 12)
    (lo := (96204833 / 500000000)) (hi := (192409667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1212167 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1212167 / 1000000) = 1/(1000000 / 1212167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (96204833 / 500000000) (192409667 / 1000000000) (Real.log (1212167 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1212167 / 1000000) = -Real.log (1000000 / 1212167) := by
    rw [show ((1212167 / 1000000) : ℝ) = ((1000000 / 1212167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (11923457 / 50000000) ≤ -Real.log (787833 / 1000000) ∧
    -Real.log (787833 / 1000000) ≤ (238469141 / 1000000000) := by
  have h := checkLog_sound (w := (212167 / 1787833)) (n := 12)
    (lo := (11923457 / 50000000)) (hi := (238469141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 787833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 787833) = 1/(787833 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-238469141 / 1000000000) (-11923457 / 50000000) (Real.log (787833 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (602585041 / 1000000000) ≤ -Real.log (25000000000 / 45670878651) ∧
    -Real.log (25000000000 / 45670878651) ≤ (301292521 / 500000000) := by
  have h := checkLog_sound (w := (20670878651 / 70670878651)) (n := 12)
    (lo := (602585041 / 1000000000)) (hi := (301292521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45670878651 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45670878651 / 25000000000) = 1/(25000000000 / 45670878651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (602585041 / 1000000000) (301292521 / 500000000) (Real.log (45670878651 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (45670878651 / 25000000000) = -Real.log (25000000000 / 45670878651) := by
    rw [show ((45670878651 / 25000000000) : ℝ) = ((25000000000 / 45670878651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (603516879 / 1000000000) ≤ -Real.log (50000000000 / 91426912693) ∧
    -Real.log (50000000000 / 91426912693) ≤ (7543961 / 12500000) := by
  have h := checkLog_sound (w := (41426912693 / 141426912693)) (n := 12)
    (lo := (603516879 / 1000000000)) (hi := (7543961 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((91426912693 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(91426912693 / 50000000000) = 1/(50000000000 / 91426912693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (603516879 / 1000000000) (7543961 / 12500000) (Real.log (91426912693 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (91426912693 / 50000000000) = -Real.log (50000000000 / 91426912693) := by
    rw [show ((91426912693 / 50000000000) : ℝ) = ((50000000000 / 91426912693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (86040481 / 200000000) ≤ -Real.log (31250000000 / 48049022021) ∧
    -Real.log (31250000000 / 48049022021) ≤ (215101203 / 500000000) := by
  have h := checkLog_sound (w := (16799022021 / 79299022021)) (n := 12)
    (lo := (86040481 / 200000000)) (hi := (215101203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48049022021 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48049022021 / 31250000000) = 1/(31250000000 / 48049022021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (86040481 / 200000000) (215101203 / 500000000) (Real.log (48049022021 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (48049022021 / 31250000000) = -Real.log (31250000000 / 48049022021) := by
    rw [show ((48049022021 / 31250000000) : ℝ) = ((31250000000 / 48049022021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (430878807 / 1000000000) ≤ -Real.log (500000000000 / 769304535353) ∧
    -Real.log (500000000000 / 769304535353) ≤ (53859851 / 125000000) := by
  have h := checkLog_sound (w := (269304535353 / 1269304535353)) (n := 12)
    (lo := (430878807 / 1000000000)) (hi := (53859851 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((769304535353 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(769304535353 / 500000000000) = 1/(500000000000 / 769304535353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (430878807 / 1000000000) (53859851 / 125000000) (Real.log (769304535353 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (769304535353 / 500000000000) = -Real.log (500000000000 / 769304535353) := by
    rw [show ((769304535353 / 500000000000) : ℝ) = ((500000000000 / 769304535353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0455
