import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0329
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

theorem reflection_log_1_neg : (217109759 / 1000000000) ≤ -Real.log (10240 / 12723) ∧
    -Real.log (10240 / 12723) ≤ (169617 / 781250) := by
  have h := checkLog_sound (w := (2483 / 22963)) (n := 12)
    (lo := (217109759 / 1000000000)) (hi := (169617 / 781250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12723 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12723 / 10240) = 1/(10240 / 12723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (217109759 / 1000000000) (169617 / 781250) (Real.log (12723 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12723 / 10240) = -Real.log (10240 / 12723) := by
    rw [show ((12723 / 10240) : ℝ) = ((10240 / 12723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (138852979 / 500000000) ≤ -Real.log (7757 / 10240) ∧
    -Real.log (7757 / 10240) ≤ (277705959 / 1000000000) := by
  have h := checkLog_sound (w := (2483 / 17997)) (n := 12)
    (lo := (138852979 / 500000000)) (hi := (277705959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7757) = 1/(7757 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-277705959 / 1000000000) (-138852979 / 500000000) (Real.log (7757 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (108436969 / 500000000) ≤ -Real.log (128 / 159) ∧
    -Real.log (128 / 159) ≤ (216873939 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 287)) (n := 12)
    (lo := (108436969 / 500000000)) (hi := (216873939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159 / 128) = 1/(128 / 159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (108436969 / 500000000) (216873939 / 1000000000) (Real.log (159 / 128)) := by
  have h := reflection_log_3_neg
  have he : Real.log (159 / 128) = -Real.log (128 / 159) := by
    rw [show ((159 / 128) : ℝ) = ((128 / 159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (55463857 / 200000000) ≤ -Real.log (97 / 128) ∧
    -Real.log (97 / 128) ≤ (138659643 / 500000000) := by
  have h := checkLog_sound (w := (31 / 225)) (n := 12)
    (lo := (55463857 / 200000000)) (hi := (138659643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 97) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 97) = 1/(97 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-138659643 / 500000000) (-55463857 / 200000000) (Real.log (97 / 128)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (395388467 / 1000000000) ≤ -Real.log (5120 / 7603) ∧
    -Real.log (5120 / 7603) ≤ (98847117 / 250000000) := by
  have h := checkLog_sound (w := (2483 / 12723)) (n := 12)
    (lo := (395388467 / 1000000000)) (hi := (98847117 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7603 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7603 / 5120) = 1/(5120 / 7603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (395388467 / 1000000000) (98847117 / 250000000) (Real.log (7603 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7603 / 5120) = -Real.log (5120 / 7603) := by
    rw [show ((7603 / 5120) : ℝ) = ((5120 / 7603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (663512531 / 1000000000) ≤ -Real.log (2637 / 5120) ∧
    -Real.log (2637 / 5120) ≤ (165878133 / 250000000) := by
  have h := checkLog_sound (w := (2483 / 7757)) (n := 12)
    (lo := (663512531 / 1000000000)) (hi := (165878133 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2637) = 1/(2637 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-165878133 / 250000000) (-663512531 / 1000000000) (Real.log (2637 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (24687113 / 62500000) ≤ -Real.log (64 / 95) ∧
    -Real.log (64 / 95) ≤ (394993809 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 159)) (n := 12)
    (lo := (24687113 / 62500000)) (hi := (394993809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95 / 64) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95 / 64) = 1/(64 / 95) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (24687113 / 62500000) (394993809 / 1000000000) (Real.log (95 / 64)) := by
  have h := reflection_log_7_neg
  have he : Real.log (95 / 64) = -Real.log (64 / 95) := by
    rw [show ((95 / 64) : ℝ) = ((64 / 95) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (662375521 / 1000000000) ≤ -Real.log (33 / 64) ∧
    -Real.log (33 / 64) ≤ (331187761 / 500000000) := by
  have h := checkLog_sound (w := (31 / 97)) (n := 12)
    (lo := (662375521 / 1000000000)) (hi := (331187761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 33) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64 / 33) = 1/(33 / 64) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-331187761 / 500000000) (-662375521 / 1000000000) (Real.log (33 / 64)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (148652561 / 500000000) ≤ -Real.log (500000 / 673113) ∧
    -Real.log (500000 / 673113) ≤ (297305123 / 1000000000) := by
  have h := checkLog_sound (w := (173113 / 1173113)) (n := 12)
    (lo := (148652561 / 500000000)) (hi := (297305123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((673113 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(673113 / 500000) = 1/(500000 / 673113) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (148652561 / 500000000) (297305123 / 1000000000) (Real.log (673113 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (673113 / 500000) = -Real.log (500000 / 673113) := by
    rw [show ((673113 / 500000) : ℝ) = ((500000 / 673113) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (26562097 / 62500000) ≤ -Real.log (326887 / 500000) ∧
    -Real.log (326887 / 500000) ≤ (424993553 / 1000000000) := by
  have h := checkLog_sound (w := (173113 / 826887)) (n := 12)
    (lo := (26562097 / 62500000)) (hi := (424993553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 326887) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 326887) = 1/(326887 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-424993553 / 1000000000) (-26562097 / 62500000) (Real.log (326887 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (148812241 / 500000000) ≤ -Real.log (31250 / 42083) ∧
    -Real.log (31250 / 42083) ≤ (297624483 / 1000000000) := by
  have h := checkLog_sound (w := (10833 / 73333)) (n := 12)
    (lo := (148812241 / 500000000)) (hi := (297624483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42083 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42083 / 31250) = 1/(31250 / 42083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (148812241 / 500000000) (297624483 / 1000000000) (Real.log (42083 / 31250)) := by
  have h := reflection_log_11_neg
  have he : Real.log (42083 / 31250) = -Real.log (31250 / 42083) := by
    rw [show ((42083 / 31250) : ℝ) = ((31250 / 42083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (425651489 / 1000000000) ≤ -Real.log (20417 / 31250) ∧
    -Real.log (20417 / 31250) ≤ (42565149 / 100000000) := by
  have h := checkLog_sound (w := (10833 / 51667)) (n := 12)
    (lo := (425651489 / 1000000000)) (hi := (42565149 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 20417) = 1/(20417 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-42565149 / 100000000) (-425651489 / 1000000000) (Real.log (20417 / 31250)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (225714643 / 1000000000) ≤ -Real.log (500000 / 626609) ∧
    -Real.log (500000 / 626609) ≤ (56428661 / 250000000) := by
  have h := checkLog_sound (w := (126609 / 1126609)) (n := 12)
    (lo := (225714643 / 1000000000)) (hi := (56428661 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((626609 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(626609 / 500000) = 1/(500000 / 626609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (225714643 / 1000000000) (56428661 / 250000000) (Real.log (626609 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (626609 / 500000) = -Real.log (500000 / 626609) := by
    rw [show ((626609 / 500000) : ℝ) = ((500000 / 626609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (29198197 / 100000000) ≤ -Real.log (373391 / 500000) ∧
    -Real.log (373391 / 500000) ≤ (291981971 / 1000000000) := by
  have h := checkLog_sound (w := (126609 / 873391)) (n := 12)
    (lo := (29198197 / 100000000)) (hi := (291981971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 373391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 373391) = 1/(373391 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-291981971 / 1000000000) (-29198197 / 100000000) (Real.log (373391 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (225982717 / 1000000000) ≤ -Real.log (500000 / 626777) ∧
    -Real.log (500000 / 626777) ≤ (112991359 / 500000000) := by
  have h := checkLog_sound (w := (126777 / 1126777)) (n := 12)
    (lo := (225982717 / 1000000000)) (hi := (112991359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((626777 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(626777 / 500000) = 1/(500000 / 626777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (225982717 / 1000000000) (112991359 / 500000000) (Real.log (626777 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (626777 / 500000) = -Real.log (500000 / 626777) := by
    rw [show ((626777 / 500000) : ℝ) = ((500000 / 626777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (146216001 / 500000000) ≤ -Real.log (373223 / 500000) ∧
    -Real.log (373223 / 500000) ≤ (292432003 / 1000000000) := by
  have h := checkLog_sound (w := (126777 / 873223)) (n := 12)
    (lo := (146216001 / 500000000)) (hi := (292432003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 373223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 373223) = 1/(373223 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-292432003 / 1000000000) (-146216001 / 500000000) (Real.log (373223 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (361149337 / 500000000) ≤ -Real.log (500000000000 / 1029580558419) ∧
    -Real.log (500000000000 / 1029580558419) ≤ (180574669 / 250000000) := by
  have h := checkLog_sound (w := (29580558419 / 2029580558419)) (n := 12)
    (lo := (14575747 / 500000000)) (hi := (5830299 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1029580558419 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1029580558419 / 1000000000000) = 1/(500000000000 / 1029580558419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (361149337 / 500000000) (180574669 / 250000000) (Real.log (1029580558419 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1029580558419 / 500000000000) = -Real.log (500000000000 / 1029580558419) := by
    rw [show ((1029580558419 / 500000000000) : ℝ) = ((500000000000 / 1029580558419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (72327597 / 100000000) ≤ -Real.log (500000000000 / 1030587255719) ∧
    -Real.log (500000000000 / 1030587255719) ≤ (180818993 / 250000000) := by
  have h := checkLog_sound (w := (30587255719 / 2030587255719)) (n := 12)
    (lo := (3012879 / 100000000)) (hi := (30128791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1030587255719 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1030587255719 / 1000000000000) = 1/(500000000000 / 1030587255719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (72327597 / 100000000) (180818993 / 250000000) (Real.log (1030587255719 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1030587255719 / 500000000000) = -Real.log (500000000000 / 1030587255719) := by
    rw [show ((1030587255719 / 500000000000) : ℝ) = ((500000000000 / 1030587255719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (517696613 / 1000000000) ≤ -Real.log (500000000000 / 839078874423) ∧
    -Real.log (500000000000 / 839078874423) ≤ (258848307 / 500000000) := by
  have h := checkLog_sound (w := (339078874423 / 1339078874423)) (n := 12)
    (lo := (517696613 / 1000000000)) (hi := (258848307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((839078874423 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(839078874423 / 500000000000) = 1/(500000000000 / 839078874423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (517696613 / 1000000000) (258848307 / 500000000) (Real.log (839078874423 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (839078874423 / 500000000000) = -Real.log (500000000000 / 839078874423) := by
    rw [show ((839078874423 / 500000000000) : ℝ) = ((500000000000 / 839078874423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (518414719 / 1000000000) ≤ -Real.log (62500000000 / 104960204757) ∧
    -Real.log (62500000000 / 104960204757) ≤ (810023 / 1562500) := by
  have h := checkLog_sound (w := (42460204757 / 167460204757)) (n := 12)
    (lo := (518414719 / 1000000000)) (hi := (810023 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((104960204757 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(104960204757 / 62500000000) = 1/(62500000000 / 104960204757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (518414719 / 1000000000) (810023 / 1562500) (Real.log (104960204757 / 62500000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (104960204757 / 62500000000) = -Real.log (62500000000 / 104960204757) := by
    rw [show ((104960204757 / 62500000000) : ℝ) = ((62500000000 / 104960204757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0329
