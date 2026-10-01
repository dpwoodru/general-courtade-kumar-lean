import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell125
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

theorem reflection_log_1_neg : (140263817 / 500000000) ≤ -Real.log (2560 / 3389) ∧
    -Real.log (2560 / 3389) ≤ (56105527 / 200000000) := by
  have h := checkLog_sound (w := (829 / 5949)) (n := 12)
    (lo := (140263817 / 500000000)) (hi := (56105527 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3389 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3389 / 2560) = 1/(2560 / 3389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (140263817 / 500000000) (56105527 / 200000000) (Real.log (3389 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3389 / 2560) = -Real.log (2560 / 3389) := by
    rw [show ((3389 / 2560) : ℝ) = ((2560 / 3389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (195653991 / 500000000) ≤ -Real.log (1731 / 2560) ∧
    -Real.log (1731 / 2560) ≤ (391307983 / 1000000000) := by
  have h := checkLog_sound (w := (829 / 4291)) (n := 12)
    (lo := (195653991 / 500000000)) (hi := (391307983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1731) = 1/(1731 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-391307983 / 1000000000) (-195653991 / 500000000) (Real.log (1731 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (280084927 / 1000000000) ≤ -Real.log (1024 / 1355) ∧
    -Real.log (1024 / 1355) ≤ (4376327 / 15625000) := by
  have h := checkLog_sound (w := (331 / 2379)) (n := 12)
    (lo := (280084927 / 1000000000)) (hi := (4376327 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1355 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1355 / 1024) = 1/(1024 / 1355) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (280084927 / 1000000000) (4376327 / 15625000) (Real.log (1355 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1355 / 1024) = -Real.log (1024 / 1355) := by
    rw [show ((1355 / 1024) : ℝ) = ((1024 / 1355) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (195220903 / 500000000) ≤ -Real.log (693 / 1024) ∧
    -Real.log (693 / 1024) ≤ (390441807 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 1717)) (n := 12)
    (lo := (195220903 / 500000000)) (hi := (390441807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 693) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 693) = 1/(693 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-390441807 / 1000000000) (-195220903 / 500000000) (Real.log (693 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (103347303 / 500000000) ≤ -Real.log (1000000 / 1229607) ∧
    -Real.log (1000000 / 1229607) ≤ (206694607 / 1000000000) := by
  have h := checkLog_sound (w := (229607 / 2229607)) (n := 12)
    (lo := (103347303 / 500000000)) (hi := (206694607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1229607 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1229607 / 1000000) = 1/(1000000 / 1229607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (103347303 / 500000000) (206694607 / 1000000000) (Real.log (1229607 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1229607 / 1000000) = -Real.log (1000000 / 1229607) := by
    rw [show ((1229607 / 1000000) : ℝ) = ((1000000 / 1229607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (32606813 / 125000000) ≤ -Real.log (770393 / 1000000) ∧
    -Real.log (770393 / 1000000) ≤ (52170901 / 200000000) := by
  have h := checkLog_sound (w := (229607 / 1770393)) (n := 12)
    (lo := (32606813 / 125000000)) (hi := (52170901 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 770393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 770393) = 1/(770393 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-52170901 / 200000000) (-32606813 / 125000000) (Real.log (770393 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (207036933 / 1000000000) ≤ -Real.log (250000 / 307507) ∧
    -Real.log (250000 / 307507) ≤ (103518467 / 500000000) := by
  have h := checkLog_sound (w := (57507 / 557507)) (n := 12)
    (lo := (207036933 / 1000000000)) (hi := (103518467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307507 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307507 / 250000) = 1/(250000 / 307507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (207036933 / 1000000000) (103518467 / 500000000) (Real.log (307507 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (307507 / 250000) = -Real.log (250000 / 307507) := by
    rw [show ((307507 / 250000) : ℝ) = ((250000 / 307507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (32675141 / 125000000) ≤ -Real.log (192493 / 250000) ∧
    -Real.log (192493 / 250000) ≤ (261401129 / 1000000000) := by
  have h := checkLog_sound (w := (57507 / 442493)) (n := 12)
    (lo := (32675141 / 125000000)) (hi := (261401129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 192493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 192493) = 1/(192493 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-261401129 / 1000000000) (-32675141 / 125000000) (Real.log (192493 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (297886 / 1953125) ≤ -Real.log (1000000 / 1164763) ∧
    -Real.log (1000000 / 1164763) ≤ (152517633 / 1000000000) := by
  have h := checkLog_sound (w := (164763 / 2164763)) (n := 12)
    (lo := (297886 / 1953125)) (hi := (152517633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1164763 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1164763 / 1000000) = 1/(1000000 / 1164763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (297886 / 1953125) (152517633 / 1000000000) (Real.log (1164763 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1164763 / 1000000) = -Real.log (1000000 / 1164763) := by
    rw [show ((1164763 / 1000000) : ℝ) = ((1000000 / 1164763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (90019881 / 500000000) ≤ -Real.log (835237 / 1000000) ∧
    -Real.log (835237 / 1000000) ≤ (180039763 / 1000000000) := by
  have h := checkLog_sound (w := (164763 / 1835237)) (n := 12)
    (lo := (90019881 / 500000000)) (hi := (180039763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 835237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 835237) = 1/(835237 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-180039763 / 1000000000) (-90019881 / 500000000) (Real.log (835237 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (76392731 / 500000000) ≤ -Real.log (40000 / 46603) ∧
    -Real.log (40000 / 46603) ≤ (152785463 / 1000000000) := by
  have h := checkLog_sound (w := (6603 / 86603)) (n := 12)
    (lo := (76392731 / 500000000)) (hi := (152785463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46603 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46603 / 40000) = 1/(40000 / 46603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (76392731 / 500000000) (152785463 / 1000000000) (Real.log (46603 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (46603 / 40000) = -Real.log (40000 / 46603) := by
    rw [show ((46603 / 40000) : ℝ) = ((40000 / 46603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (90206689 / 500000000) ≤ -Real.log (33397 / 40000) ∧
    -Real.log (33397 / 40000) ≤ (180413379 / 1000000000) := by
  have h := checkLog_sound (w := (6603 / 73397)) (n := 12)
    (lo := (90206689 / 500000000)) (hi := (180413379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 33397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 33397) = 1/(33397 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-180413379 / 1000000000) (-90206689 / 500000000) (Real.log (33397 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (335263367 / 500000000) ≤ -Real.log (500000000000 / 977633477633) ∧
    -Real.log (500000000000 / 977633477633) ≤ (134105347 / 200000000) := by
  have h := checkLog_sound (w := (477633477633 / 1477633477633)) (n := 12)
    (lo := (335263367 / 500000000)) (hi := (134105347 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((977633477633 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(977633477633 / 500000000000) = 1/(500000000000 / 977633477633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (335263367 / 500000000) (134105347 / 200000000) (Real.log (977633477633 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (977633477633 / 500000000000) = -Real.log (500000000000 / 977633477633) := by
    rw [show ((977633477633 / 500000000000) : ℝ) = ((500000000000 / 977633477633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (20994863 / 31250000) ≤ -Real.log (500000000000 / 978913922589) ∧
    -Real.log (500000000000 / 978913922589) ≤ (671835617 / 1000000000) := by
  have h := checkLog_sound (w := (478913922589 / 1478913922589)) (n := 12)
    (lo := (20994863 / 31250000)) (hi := (671835617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((978913922589 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(978913922589 / 500000000000) = 1/(500000000000 / 978913922589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (20994863 / 31250000) (671835617 / 1000000000) (Real.log (978913922589 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (978913922589 / 500000000000) = -Real.log (500000000000 / 978913922589) := by
    rw [show ((978913922589 / 500000000000) : ℝ) = ((500000000000 / 978913922589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (46754911 / 100000000) ≤ -Real.log (500000000000 / 798038793187) ∧
    -Real.log (500000000000 / 798038793187) ≤ (467549111 / 1000000000) := by
  have h := checkLog_sound (w := (298038793187 / 1298038793187)) (n := 12)
    (lo := (46754911 / 100000000)) (hi := (467549111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((798038793187 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(798038793187 / 500000000000) = 1/(500000000000 / 798038793187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (46754911 / 100000000) (467549111 / 1000000000) (Real.log (798038793187 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (798038793187 / 500000000000) = -Real.log (500000000000 / 798038793187) := by
    rw [show ((798038793187 / 500000000000) : ℝ) = ((500000000000 / 798038793187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (468438061 / 1000000000) ≤ -Real.log (500000000000 / 798748525921) ∧
    -Real.log (500000000000 / 798748525921) ≤ (234219031 / 500000000) := by
  have h := checkLog_sound (w := (298748525921 / 1298748525921)) (n := 12)
    (lo := (468438061 / 1000000000)) (hi := (234219031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((798748525921 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(798748525921 / 500000000000) = 1/(500000000000 / 798748525921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (468438061 / 1000000000) (234219031 / 500000000) (Real.log (798748525921 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (798748525921 / 500000000000) = -Real.log (500000000000 / 798748525921) := by
    rw [show ((798748525921 / 500000000000) : ℝ) = ((500000000000 / 798748525921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (166278697 / 500000000) ≤ -Real.log (500000000000 / 697264967907) ∧
    -Real.log (500000000000 / 697264967907) ≤ (66511479 / 200000000) := by
  have h := checkLog_sound (w := (197264967907 / 1197264967907)) (n := 12)
    (lo := (166278697 / 500000000)) (hi := (66511479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697264967907 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697264967907 / 500000000000) = 1/(500000000000 / 697264967907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (166278697 / 500000000) (66511479 / 200000000) (Real.log (697264967907 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (697264967907 / 500000000000) = -Real.log (500000000000 / 697264967907) := by
    rw [show ((697264967907 / 500000000000) : ℝ) = ((500000000000 / 697264967907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (333198841 / 1000000000) ≤ -Real.log (800000000 / 1116339791) ∧
    -Real.log (800000000 / 1116339791) ≤ (166599421 / 500000000) := by
  have h := checkLog_sound (w := (316339791 / 1916339791)) (n := 12)
    (lo := (333198841 / 1000000000)) (hi := (166599421 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1116339791 / 800000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1116339791 / 800000000) = 1/(800000000 / 1116339791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (333198841 / 1000000000) (166599421 / 500000000) (Real.log (1116339791 / 800000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1116339791 / 800000000) = -Real.log (800000000 / 1116339791) := by
    rw [show ((1116339791 / 800000000) : ℝ) = ((800000000 / 1116339791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (5525583 / 200000000) ≤ -Real.log (1556400391 / 1600000000) ∧
    -Real.log (1556400391 / 1600000000) ≤ (6906979 / 250000000) := by
  have h := checkLog_sound (w := (43599609 / 3156400391)) (n := 12)
    (lo := (5525583 / 200000000)) (hi := (6906979 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1556400391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1556400391) = 1/(1556400391 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-6906979 / 250000000) (-5525583 / 200000000) (Real.log (1556400391 / 1600000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (27522129 / 1000000000) ≤ -Real.log (972853153831 / 1000000000000) ∧
    -Real.log (972853153831 / 1000000000000) ≤ (2752213 / 100000000) := by
  have h := checkLog_sound (w := (27146846169 / 1972853153831)) (n := 12)
    (lo := (27522129 / 1000000000)) (hi := (2752213 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 972853153831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 972853153831) = 1/(972853153831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2752213 / 100000000) (-27522129 / 1000000000) (Real.log (972853153831 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell125
