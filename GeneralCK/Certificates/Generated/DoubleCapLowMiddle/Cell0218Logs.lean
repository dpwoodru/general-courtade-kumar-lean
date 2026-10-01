import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0218
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

theorem reflection_log_1_neg : (531179569 / 1000000000) ≤ -Real.log (3200 / 5443) ∧
    -Real.log (3200 / 5443) ≤ (53117957 / 100000000) := by
  have h := checkLog_sound (w := (2243 / 8643)) (n := 12)
    (lo := (531179569 / 1000000000)) (hi := (53117957 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5443 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5443 / 3200) = 1/(3200 / 5443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (531179569 / 1000000000) (53117957 / 100000000) (Real.log (5443 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5443 / 3200) = -Real.log (3200 / 5443) := by
    rw [show ((5443 / 3200) : ℝ) = ((3200 / 5443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (150887837 / 125000000) ≤ -Real.log (957 / 3200) ∧
    -Real.log (957 / 3200) ≤ (603551349 / 500000000) := by
  have h := checkLog_sound (w := (643 / 2557)) (n := 12)
    (lo := (128488879 / 250000000)) (hi := (513955517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 957) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 957) = 1/(957 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-603551349 / 500000000) (-150887837 / 125000000) (Real.log (957 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (26384137 / 50000000) ≤ -Real.log (200 / 339) ∧
    -Real.log (200 / 339) ≤ (527682741 / 1000000000) := by
  have h := checkLog_sound (w := (139 / 539)) (n := 12)
    (lo := (26384137 / 50000000)) (hi := (527682741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339 / 200) = 1/(200 / 339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (26384137 / 50000000) (527682741 / 1000000000) (Real.log (339 / 200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (339 / 200) = -Real.log (200 / 339) := by
    rw [show ((339 / 200) : ℝ) = ((200 / 339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1187443501 / 1000000000) ≤ -Real.log (61 / 200) ∧
    -Real.log (61 / 200) ≤ (1187443503 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 161)) (n := 12)
    (lo := (494296321 / 1000000000)) (hi := (247148161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 61) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100 / 61) = 1/(61 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1187443503 / 1000000000) (-1187443501 / 1000000000) (Real.log (61 / 200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (168905313 / 500000000) ≤ -Real.log (1600 / 2243) ∧
    -Real.log (1600 / 2243) ≤ (337810627 / 1000000000) := by
  have h := checkLog_sound (w := (643 / 3843)) (n := 12)
    (lo := (168905313 / 500000000)) (hi := (337810627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2243 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2243 / 1600) = 1/(1600 / 2243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (168905313 / 500000000) (337810627 / 1000000000) (Real.log (2243 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2243 / 1600) = -Real.log (1600 / 2243) := by
    rw [show ((2243 / 1600) : ℝ) = ((1600 / 2243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (128488879 / 250000000) ≤ -Real.log (957 / 1600) ∧
    -Real.log (957 / 1600) ≤ (513955517 / 1000000000) := by
  have h := checkLog_sound (w := (643 / 2557)) (n := 12)
    (lo := (128488879 / 250000000)) (hi := (513955517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 957) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600 / 957) = 1/(957 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-513955517 / 1000000000) (-128488879 / 250000000) (Real.log (957 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (329303747 / 1000000000) ≤ -Real.log (100 / 139) ∧
    -Real.log (100 / 139) ≤ (82325937 / 250000000) := by
  have h := checkLog_sound (w := (39 / 239)) (n := 12)
    (lo := (329303747 / 1000000000)) (hi := (82325937 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139 / 100) = 1/(100 / 139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (329303747 / 1000000000) (82325937 / 250000000) (Real.log (139 / 100)) := by
  have h := reflection_log_7_neg
  have he : Real.log (139 / 100) = -Real.log (100 / 139) := by
    rw [show ((139 / 100) : ℝ) = ((100 / 139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (494296321 / 1000000000) ≤ -Real.log (61 / 100) ∧
    -Real.log (61 / 100) ≤ (247148161 / 500000000) := by
  have h := checkLog_sound (w := (39 / 161)) (n := 12)
    (lo := (494296321 / 1000000000)) (hi := (247148161 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 61) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 61) = 1/(61 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-247148161 / 500000000) (-494296321 / 1000000000) (Real.log (61 / 100)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (596452893 / 1000000000) ≤ -Real.log (1000000 / 1815667) ∧
    -Real.log (1000000 / 1815667) ≤ (298226447 / 500000000) := by
  have h := checkLog_sound (w := (815667 / 2815667)) (n := 12)
    (lo := (596452893 / 1000000000)) (hi := (298226447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1815667 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1815667 / 1000000) = 1/(1000000 / 1815667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (596452893 / 1000000000) (298226447 / 500000000) (Real.log (1815667 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1815667 / 1000000) = -Real.log (1000000 / 1815667) := by
    rw [show ((1815667 / 1000000) : ℝ) = ((1000000 / 1815667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1691011373 / 1000000000) ≤ -Real.log (184333 / 1000000) ∧
    -Real.log (184333 / 1000000) ≤ (105688211 / 62500000) := by
  have h := checkLog_sound (w := (65667 / 434333)) (n := 12)
    (lo := (304717013 / 1000000000)) (hi := (152358507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 184333) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 184333) = 1/(184333 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-105688211 / 62500000) (-1691011373 / 1000000000) (Real.log (184333 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (149411833 / 250000000) ≤ -Real.log (1000000 / 1817837) ∧
    -Real.log (1000000 / 1817837) ≤ (597647333 / 1000000000) := by
  have h := checkLog_sound (w := (817837 / 2817837)) (n := 12)
    (lo := (149411833 / 250000000)) (hi := (597647333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1817837 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1817837 / 1000000) = 1/(1000000 / 1817837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (149411833 / 250000000) (597647333 / 1000000000) (Real.log (1817837 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1817837 / 1000000) = -Real.log (1000000 / 1817837) := by
    rw [show ((1817837 / 1000000) : ℝ) = ((1000000 / 1817837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1702853387 / 1000000000) ≤ -Real.log (182163 / 1000000) ∧
    -Real.log (182163 / 1000000) ≤ (170285339 / 100000000) := by
  have h := checkLog_sound (w := (67837 / 432163)) (n := 12)
    (lo := (316559027 / 1000000000)) (hi := (79139757 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 182163) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 182163) = 1/(182163 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-170285339 / 100000000) (-1702853387 / 1000000000) (Real.log (182163 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (288567569 / 500000000) ≤ -Real.log (1000000 / 1780929) ∧
    -Real.log (1000000 / 1780929) ≤ (577135139 / 1000000000) := by
  have h := checkLog_sound (w := (780929 / 2780929)) (n := 12)
    (lo := (288567569 / 500000000)) (hi := (577135139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1780929 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1780929 / 1000000) = 1/(1000000 / 1780929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (288567569 / 500000000) (577135139 / 1000000000) (Real.log (1780929 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1780929 / 1000000) = -Real.log (1000000 / 1780929) := by
    rw [show ((1780929 / 1000000) : ℝ) = ((1000000 / 1780929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1518359399 / 1000000000) ≤ -Real.log (219071 / 1000000) ∧
    -Real.log (219071 / 1000000) ≤ (759179701 / 500000000) := by
  have h := checkLog_sound (w := (30929 / 469071)) (n := 12)
    (lo := (132065039 / 1000000000)) (hi := (1650813 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 219071) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 219071) = 1/(219071 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-759179701 / 500000000) (-1518359399 / 1000000000) (Real.log (219071 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (9051303 / 15625000) ≤ -Real.log (1000000 / 1784759) ∧
    -Real.log (1000000 / 1784759) ≤ (579283393 / 1000000000) := by
  have h := checkLog_sound (w := (784759 / 2784759)) (n := 12)
    (lo := (9051303 / 15625000)) (hi := (579283393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1784759 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1784759 / 1000000) = 1/(1000000 / 1784759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (9051303 / 15625000) (579283393 / 1000000000) (Real.log (1784759 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1784759 / 1000000) = -Real.log (1000000 / 1784759) := by
    rw [show ((1784759 / 1000000) : ℝ) = ((1000000 / 1784759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1535996947 / 1000000000) ≤ -Real.log (215241 / 1000000) ∧
    -Real.log (215241 / 1000000) ≤ (30719939 / 20000000) := by
  have h := checkLog_sound (w := (34759 / 465241)) (n := 12)
    (lo := (149702587 / 1000000000)) (hi := (37425647 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 215241) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 215241) = 1/(215241 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-30719939 / 20000000) (-1535996947 / 1000000000) (Real.log (215241 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1143732133 / 500000000) ≤ -Real.log (100000000000 / 984992920421) ∧
    -Real.log (100000000000 / 984992920421) ≤ (228746427 / 100000000) := by
  have h := checkLog_sound (w := (184992920421 / 1784992920421)) (n := 12)
    (lo := (104011363 / 500000000)) (hi := (208022727 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((984992920421 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(984992920421 / 800000000000) = 1/(100000000000 / 984992920421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1143732133 / 500000000) (228746427 / 100000000) (Real.log (984992920421 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (984992920421 / 100000000000) = -Real.log (100000000000 / 984992920421) := by
    rw [show ((984992920421 / 100000000000) : ℝ) = ((100000000000 / 984992920421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2300500719 / 1000000000) ≤ -Real.log (62500000000 / 623698624309) ∧
    -Real.log (62500000000 / 623698624309) ≤ (2300500723 / 1000000000) := by
  have h := checkLog_sound (w := (123698624309 / 1123698624309)) (n := 12)
    (lo := (221059179 / 1000000000)) (hi := (11052959 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((623698624309 / 500000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(623698624309 / 500000000000) = 1/(62500000000 / 623698624309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2300500719 / 1000000000) (2300500723 / 1000000000) (Real.log (623698624309 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (623698624309 / 62500000000) = -Real.log (62500000000 / 623698624309) := by
    rw [show ((623698624309 / 62500000000) : ℝ) = ((62500000000 / 623698624309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2095494537 / 1000000000) ≤ -Real.log (62500000000 / 508091269497) ∧
    -Real.log (62500000000 / 508091269497) ≤ (2095494541 / 1000000000) := by
  have h := checkLog_sound (w := (8091269497 / 1008091269497)) (n := 12)
    (lo := (16052997 / 1000000000)) (hi := (8026499 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((508091269497 / 500000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(508091269497 / 500000000000) = 1/(62500000000 / 508091269497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2095494537 / 1000000000) (2095494541 / 1000000000) (Real.log (508091269497 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (508091269497 / 62500000000) = -Real.log (62500000000 / 508091269497) := by
    rw [show ((508091269497 / 62500000000) : ℝ) = ((62500000000 / 508091269497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1057640169 / 500000000) ≤ -Real.log (6250000000 / 51824437491) ∧
    -Real.log (6250000000 / 51824437491) ≤ (1057640171 / 500000000) := by
  have h := checkLog_sound (w := (1824437491 / 101824437491)) (n := 12)
    (lo := (17919399 / 500000000)) (hi := (35838799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51824437491 / 50000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(51824437491 / 50000000000) = 1/(6250000000 / 51824437491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1057640169 / 500000000) (1057640171 / 500000000) (Real.log (51824437491 / 6250000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (51824437491 / 6250000000) = -Real.log (6250000000 / 51824437491) := by
    rw [show ((51824437491 / 6250000000) : ℝ) = ((6250000000 / 51824437491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0218
