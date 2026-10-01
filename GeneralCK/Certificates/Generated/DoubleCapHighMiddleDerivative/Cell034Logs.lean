import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell034
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

theorem reflection_log_1_neg : (7481771 / 31250000) ≤ -Real.log (1024 / 1301) ∧
    -Real.log (1024 / 1301) ≤ (239416673 / 1000000000) := by
  have h := checkLog_sound (w := (277 / 2325)) (n := 12)
    (lo := (7481771 / 31250000)) (hi := (239416673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1301 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1301 / 1024) = 1/(1024 / 1301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (7481771 / 31250000) (239416673 / 1000000000) (Real.log (1301 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1301 / 1024) = -Real.log (1024 / 1301) := by
    rw [show ((1301 / 1024) : ℝ) = ((1024 / 1301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (15770331 / 50000000) ≤ -Real.log (747 / 1024) ∧
    -Real.log (747 / 1024) ≤ (315406621 / 1000000000) := by
  have h := checkLog_sound (w := (277 / 1771)) (n := 12)
    (lo := (15770331 / 50000000)) (hi := (315406621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 747) = 1/(747 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-315406621 / 1000000000) (-15770331 / 50000000) (Real.log (747 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (119477691 / 500000000) ≤ -Real.log (2560 / 3251) ∧
    -Real.log (2560 / 3251) ≤ (238955383 / 1000000000) := by
  have h := checkLog_sound (w := (691 / 5811)) (n := 12)
    (lo := (119477691 / 500000000)) (hi := (238955383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3251 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3251 / 2560) = 1/(2560 / 3251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (119477691 / 500000000) (238955383 / 1000000000) (Real.log (3251 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3251 / 2560) = -Real.log (2560 / 3251) := by
    rw [show ((3251 / 2560) : ℝ) = ((2560 / 3251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (31460373 / 100000000) ≤ -Real.log (1869 / 2560) ∧
    -Real.log (1869 / 2560) ≤ (314603731 / 1000000000) := by
  have h := checkLog_sound (w := (691 / 4429)) (n := 12)
    (lo := (31460373 / 100000000)) (hi := (314603731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1869) = 1/(1869 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-314603731 / 1000000000) (-31460373 / 100000000) (Real.log (1869 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (35036057 / 200000000) ≤ -Real.log (1000000 / 1191461) ∧
    -Real.log (1000000 / 1191461) ≤ (87590143 / 500000000) := by
  have h := checkLog_sound (w := (191461 / 2191461)) (n := 12)
    (lo := (35036057 / 200000000)) (hi := (87590143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1191461 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1191461 / 1000000) = 1/(1000000 / 1191461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (35036057 / 200000000) (87590143 / 500000000) (Real.log (1191461 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1191461 / 1000000) = -Real.log (1000000 / 1191461) := by
    rw [show ((1191461 / 1000000) : ℝ) = ((1000000 / 1191461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (212526363 / 1000000000) ≤ -Real.log (808539 / 1000000) ∧
    -Real.log (808539 / 1000000) ≤ (53131591 / 250000000) := by
  have h := checkLog_sound (w := (191461 / 1808539)) (n := 12)
    (lo := (212526363 / 1000000000)) (hi := (53131591 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 808539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 808539) = 1/(808539 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-53131591 / 250000000) (-212526363 / 1000000000) (Real.log (808539 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (43882973 / 250000000) ≤ -Real.log (25000 / 29797) ∧
    -Real.log (25000 / 29797) ≤ (175531893 / 1000000000) := by
  have h := checkLog_sound (w := (4797 / 54797)) (n := 12)
    (lo := (43882973 / 250000000)) (hi := (175531893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29797 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29797 / 25000) = 1/(25000 / 29797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (43882973 / 250000000) (175531893 / 1000000000) (Real.log (29797 / 25000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (29797 / 25000) = -Real.log (25000 / 29797) := by
    rw [show ((29797 / 25000) : ℝ) = ((25000 / 29797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (53261179 / 250000000) ≤ -Real.log (20203 / 25000) ∧
    -Real.log (20203 / 25000) ≤ (213044717 / 1000000000) := by
  have h := checkLog_sound (w := (4797 / 45203)) (n := 12)
    (lo := (53261179 / 250000000)) (hi := (213044717 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 20203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 20203) = 1/(20203 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-213044717 / 1000000000) (-53261179 / 250000000) (Real.log (20203 / 25000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (64096773 / 500000000) ≤ -Real.log (1000000 / 1136773) ∧
    -Real.log (1000000 / 1136773) ≤ (128193547 / 1000000000) := by
  have h := checkLog_sound (w := (136773 / 2136773)) (n := 12)
    (lo := (64096773 / 500000000)) (hi := (128193547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1136773 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1136773 / 1000000) = 1/(1000000 / 1136773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (64096773 / 500000000) (128193547 / 1000000000) (Real.log (1136773 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1136773 / 1000000) = -Real.log (1000000 / 1136773) := by
    rw [show ((1136773 / 1000000) : ℝ) = ((1000000 / 1136773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (73538793 / 500000000) ≤ -Real.log (863227 / 1000000) ∧
    -Real.log (863227 / 1000000) ≤ (147077587 / 1000000000) := by
  have h := checkLog_sound (w := (136773 / 1863227)) (n := 12)
    (lo := (73538793 / 500000000)) (hi := (147077587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 863227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 863227) = 1/(863227 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-147077587 / 1000000000) (-73538793 / 500000000) (Real.log (863227 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (128462693 / 1000000000) ≤ -Real.log (1000000 / 1137079) ∧
    -Real.log (1000000 / 1137079) ≤ (64231347 / 500000000) := by
  have h := checkLog_sound (w := (137079 / 2137079)) (n := 12)
    (lo := (128462693 / 1000000000)) (hi := (64231347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1137079 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1137079 / 1000000) = 1/(1000000 / 1137079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (128462693 / 1000000000) (64231347 / 500000000) (Real.log (1137079 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1137079 / 1000000) = -Real.log (1000000 / 1137079) := by
    rw [show ((1137079 / 1000000) : ℝ) = ((1000000 / 1137079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (147432133 / 1000000000) ≤ -Real.log (862921 / 1000000) ∧
    -Real.log (862921 / 1000000) ≤ (73716067 / 500000000) := by
  have h := checkLog_sound (w := (137079 / 1862921)) (n := 12)
    (lo := (147432133 / 1000000000)) (hi := (73716067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 862921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 862921) = 1/(862921 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-73716067 / 500000000) (-147432133 / 1000000000) (Real.log (862921 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (69194889 / 125000000) ≤ -Real.log (62500000000 / 108714553237) ∧
    -Real.log (62500000000 / 108714553237) ≤ (553559113 / 1000000000) := by
  have h := checkLog_sound (w := (46214553237 / 171214553237)) (n := 12)
    (lo := (69194889 / 125000000)) (hi := (553559113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108714553237 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108714553237 / 62500000000) = 1/(62500000000 / 108714553237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (69194889 / 125000000) (553559113 / 1000000000) (Real.log (108714553237 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (108714553237 / 62500000000) = -Real.log (62500000000 / 108714553237) := by
    rw [show ((108714553237 / 62500000000) : ℝ) = ((62500000000 / 108714553237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (554823293 / 1000000000) ≤ -Real.log (500000000000 / 870816599733) ∧
    -Real.log (500000000000 / 870816599733) ≤ (277411647 / 500000000) := by
  have h := checkLog_sound (w := (370816599733 / 1370816599733)) (n := 12)
    (lo := (554823293 / 1000000000)) (hi := (277411647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((870816599733 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(870816599733 / 500000000000) = 1/(500000000000 / 870816599733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (554823293 / 1000000000) (277411647 / 500000000) (Real.log (870816599733 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (870816599733 / 500000000000) = -Real.log (500000000000 / 870816599733) := by
    rw [show ((870816599733 / 500000000000) : ℝ) = ((500000000000 / 870816599733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (48463331 / 125000000) ≤ -Real.log (100000000000 / 147359743933) ∧
    -Real.log (100000000000 / 147359743933) ≤ (387706649 / 1000000000) := by
  have h := checkLog_sound (w := (47359743933 / 247359743933)) (n := 12)
    (lo := (48463331 / 125000000)) (hi := (387706649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147359743933 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147359743933 / 100000000000) = 1/(100000000000 / 147359743933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (48463331 / 125000000) (387706649 / 1000000000) (Real.log (147359743933 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (147359743933 / 100000000000) = -Real.log (100000000000 / 147359743933) := by
    rw [show ((147359743933 / 100000000000) : ℝ) = ((100000000000 / 147359743933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (388576609 / 1000000000) ≤ -Real.log (500000000000 / 737439984161) ∧
    -Real.log (500000000000 / 737439984161) ≤ (38857661 / 100000000) := by
  have h := checkLog_sound (w := (237439984161 / 1237439984161)) (n := 12)
    (lo := (388576609 / 1000000000)) (hi := (38857661 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((737439984161 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(737439984161 / 500000000000) = 1/(500000000000 / 737439984161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (388576609 / 1000000000) (38857661 / 100000000) (Real.log (737439984161 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (737439984161 / 500000000000) = -Real.log (500000000000 / 737439984161) := by
    rw [show ((737439984161 / 500000000000) : ℝ) = ((500000000000 / 737439984161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (275271133 / 1000000000) ≤ -Real.log (500000000000 / 658443839221) ∧
    -Real.log (500000000000 / 658443839221) ≤ (137635567 / 500000000) := by
  have h := checkLog_sound (w := (158443839221 / 1158443839221)) (n := 12)
    (lo := (275271133 / 1000000000)) (hi := (137635567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((658443839221 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(658443839221 / 500000000000) = 1/(500000000000 / 658443839221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (275271133 / 1000000000) (137635567 / 500000000) (Real.log (658443839221 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (658443839221 / 500000000000) = -Real.log (500000000000 / 658443839221) := by
    rw [show ((658443839221 / 500000000000) : ℝ) = ((500000000000 / 658443839221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (137947413 / 500000000) ≤ -Real.log (250000000000 / 329427317217) ∧
    -Real.log (250000000000 / 329427317217) ≤ (275894827 / 1000000000) := by
  have h := checkLog_sound (w := (79427317217 / 579427317217)) (n := 12)
    (lo := (137947413 / 500000000)) (hi := (275894827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329427317217 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329427317217 / 250000000000) = 1/(250000000000 / 329427317217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (137947413 / 500000000) (275894827 / 1000000000) (Real.log (329427317217 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (329427317217 / 250000000000) = -Real.log (250000000000 / 329427317217) := by
    rw [show ((329427317217 / 250000000000) : ℝ) = ((250000000000 / 329427317217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (18969439 / 1000000000) ≤ -Real.log (981209347759 / 1000000000000) ∧
    -Real.log (981209347759 / 1000000000000) ≤ (118559 / 6250000) := by
  have h := checkLog_sound (w := (18790652241 / 1981209347759)) (n := 12)
    (lo := (18969439 / 1000000000)) (hi := (118559 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981209347759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981209347759) = 1/(981209347759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-118559 / 6250000) (-18969439 / 1000000000) (Real.log (981209347759 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (18884039 / 1000000000) ≤ -Real.log (981293146471 / 1000000000000) ∧
    -Real.log (981293146471 / 1000000000000) ≤ (472101 / 25000000) := by
  have h := checkLog_sound (w := (18706853529 / 1981293146471)) (n := 12)
    (lo := (18884039 / 1000000000)) (hi := (472101 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 981293146471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 981293146471) = 1/(981293146471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-472101 / 25000000) (-18884039 / 1000000000) (Real.log (981293146471 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell034
