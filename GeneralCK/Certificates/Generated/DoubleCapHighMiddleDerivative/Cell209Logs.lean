import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell209
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

theorem reflection_log_1_neg : (158516133 / 500000000) ≤ -Real.log (512 / 703) ∧
    -Real.log (512 / 703) ≤ (317032267 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 1215)) (n := 12)
    (lo := (158516133 / 500000000)) (hi := (317032267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((703 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(703 / 512) = 1/(512 / 703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (158516133 / 500000000) (317032267 / 1000000000) (Real.log (703 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (703 / 512) = -Real.log (512 / 703) := by
    rw [show ((703 / 512) : ℝ) = ((512 / 703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (466883501 / 1000000000) ≤ -Real.log (321 / 512) ∧
    -Real.log (321 / 512) ≤ (233441751 / 500000000) := by
  have h := checkLog_sound (w := (191 / 833)) (n := 12)
    (lo := (466883501 / 1000000000)) (hi := (233441751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 321) = 1/(321 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-233441751 / 500000000) (-466883501 / 1000000000) (Real.log (321 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (316605433 / 1000000000) ≤ -Real.log (5120 / 7027) ∧
    -Real.log (5120 / 7027) ≤ (158302717 / 500000000) := by
  have h := checkLog_sound (w := (1907 / 12147)) (n := 12)
    (lo := (316605433 / 1000000000)) (hi := (158302717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7027 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7027 / 5120) = 1/(5120 / 7027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (316605433 / 1000000000) (158302717 / 500000000) (Real.log (7027 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7027 / 5120) = -Real.log (5120 / 7027) := by
    rw [show ((7027 / 5120) : ℝ) = ((5120 / 7027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (232974679 / 500000000) ≤ -Real.log (3213 / 5120) ∧
    -Real.log (3213 / 5120) ≤ (465949359 / 1000000000) := by
  have h := checkLog_sound (w := (1907 / 8333)) (n := 12)
    (lo := (232974679 / 500000000)) (hi := (465949359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3213) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3213) = 1/(3213 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-465949359 / 1000000000) (-232974679 / 500000000) (Real.log (3213 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (117530527 / 500000000) ≤ -Real.log (500000 / 632493) ∧
    -Real.log (500000 / 632493) ≤ (47012211 / 200000000) := by
  have h := checkLog_sound (w := (132493 / 1132493)) (n := 12)
    (lo := (117530527 / 500000000)) (hi := (47012211 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((632493 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(632493 / 500000) = 1/(500000 / 632493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (117530527 / 500000000) (47012211 / 200000000) (Real.log (632493 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (632493 / 500000) = -Real.log (500000 / 632493) := by
    rw [show ((632493 / 500000) : ℝ) = ((500000 / 632493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (76966433 / 250000000) ≤ -Real.log (367507 / 500000) ∧
    -Real.log (367507 / 500000) ≤ (307865733 / 1000000000) := by
  have h := checkLog_sound (w := (132493 / 867507)) (n := 12)
    (lo := (76966433 / 250000000)) (hi := (307865733 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 367507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 367507) = 1/(367507 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-307865733 / 1000000000) (-76966433 / 250000000) (Real.log (367507 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23539539 / 100000000) ≤ -Real.log (1000000 / 1265409) ∧
    -Real.log (1000000 / 1265409) ≤ (235395391 / 1000000000) := by
  have h := checkLog_sound (w := (265409 / 2265409)) (n := 12)
    (lo := (23539539 / 100000000)) (hi := (235395391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1265409 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1265409 / 1000000) = 1/(1000000 / 1265409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (23539539 / 100000000) (235395391 / 1000000000) (Real.log (1265409 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1265409 / 1000000) = -Real.log (1000000 / 1265409) := by
    rw [show ((1265409 / 1000000) : ℝ) = ((1000000 / 1265409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (308441397 / 1000000000) ≤ -Real.log (734591 / 1000000) ∧
    -Real.log (734591 / 1000000) ≤ (154220699 / 500000000) := by
  have h := checkLog_sound (w := (265409 / 1734591)) (n := 12)
    (lo := (308441397 / 1000000000)) (hi := (154220699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 734591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 734591) = 1/(734591 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-154220699 / 500000000) (-308441397 / 1000000000) (Real.log (734591 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (87434427 / 500000000) ≤ -Real.log (100000 / 119109) ∧
    -Real.log (100000 / 119109) ≤ (34973771 / 200000000) := by
  have h := checkLog_sound (w := (19109 / 219109)) (n := 12)
    (lo := (87434427 / 500000000)) (hi := (34973771 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119109 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119109 / 100000) = 1/(100000 / 119109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (87434427 / 500000000) (34973771 / 200000000) (Real.log (119109 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (119109 / 100000) = -Real.log (100000 / 119109) := by
    rw [show ((119109 / 100000) : ℝ) = ((100000 / 119109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (6627113 / 31250000) ≤ -Real.log (80891 / 100000) ∧
    -Real.log (80891 / 100000) ≤ (212067617 / 1000000000) := by
  have h := checkLog_sound (w := (19109 / 180891)) (n := 12)
    (lo := (6627113 / 31250000)) (hi := (212067617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 80891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 80891) = 1/(80891 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-212067617 / 1000000000) (-6627113 / 31250000) (Real.log (80891 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (175134961 / 1000000000) ≤ -Real.log (1000000 / 1191407) ∧
    -Real.log (1000000 / 1191407) ≤ (87567481 / 500000000) := by
  have h := checkLog_sound (w := (191407 / 2191407)) (n := 12)
    (lo := (175134961 / 1000000000)) (hi := (87567481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1191407 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1191407 / 1000000) = 1/(1000000 / 1191407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (175134961 / 1000000000) (87567481 / 500000000) (Real.log (1191407 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1191407 / 1000000) = -Real.log (1000000 / 1191407) := by
    rw [show ((1191407 / 1000000) : ℝ) = ((1000000 / 1191407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (106229789 / 500000000) ≤ -Real.log (808593 / 1000000) ∧
    -Real.log (808593 / 1000000) ≤ (212459579 / 1000000000) := by
  have h := checkLog_sound (w := (191407 / 1808593)) (n := 12)
    (lo := (106229789 / 500000000)) (hi := (212459579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 808593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 808593) = 1/(808593 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-212459579 / 1000000000) (-106229789 / 500000000) (Real.log (808593 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (782554791 / 1000000000) ≤ -Real.log (31250000000 / 68345393713) ∧
    -Real.log (31250000000 / 68345393713) ≤ (782554793 / 1000000000) := by
  have h := checkLog_sound (w := (5845393713 / 130845393713)) (n := 12)
    (lo := (89407611 / 1000000000)) (hi := (22351903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68345393713 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(68345393713 / 62500000000) = 1/(31250000000 / 68345393713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (782554791 / 1000000000) (782554793 / 1000000000) (Real.log (68345393713 / 31250000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (68345393713 / 31250000000) = -Real.log (31250000000 / 68345393713) := by
    rw [show ((68345393713 / 31250000000) : ℝ) = ((31250000000 / 68345393713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (97989471 / 125000000) ≤ -Real.log (125000000000 / 273753894081) ∧
    -Real.log (125000000000 / 273753894081) ≤ (78391577 / 100000000) := by
  have h := checkLog_sound (w := (23753894081 / 523753894081)) (n := 12)
    (lo := (22692147 / 250000000)) (hi := (90768589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273753894081 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(273753894081 / 250000000000) = 1/(125000000000 / 273753894081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (97989471 / 125000000) (78391577 / 100000000) (Real.log (273753894081 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (273753894081 / 125000000000) = -Real.log (125000000000 / 273753894081) := by
    rw [show ((273753894081 / 125000000000) : ℝ) = ((125000000000 / 273753894081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (542926787 / 1000000000) ≤ -Real.log (125000000000 / 215129575763) ∧
    -Real.log (125000000000 / 215129575763) ≤ (135731697 / 250000000) := by
  have h := checkLog_sound (w := (90129575763 / 340129575763)) (n := 12)
    (lo := (542926787 / 1000000000)) (hi := (135731697 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215129575763 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215129575763 / 125000000000) = 1/(125000000000 / 215129575763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (542926787 / 1000000000) (135731697 / 250000000) (Real.log (215129575763 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (215129575763 / 125000000000) = -Real.log (125000000000 / 215129575763) := by
    rw [show ((215129575763 / 125000000000) : ℝ) = ((125000000000 / 215129575763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (543836787 / 1000000000) ≤ -Real.log (15625000000 / 26915679099) ∧
    -Real.log (15625000000 / 26915679099) ≤ (135959197 / 250000000) := by
  have h := checkLog_sound (w := (11290679099 / 42540679099)) (n := 12)
    (lo := (543836787 / 1000000000)) (hi := (135959197 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26915679099 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(26915679099 / 15625000000) = 1/(15625000000 / 26915679099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (543836787 / 1000000000) (135959197 / 250000000) (Real.log (26915679099 / 15625000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (26915679099 / 15625000000) = -Real.log (15625000000 / 26915679099) := by
    rw [show ((26915679099 / 15625000000) : ℝ) = ((15625000000 / 26915679099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (38693647 / 100000000) ≤ -Real.log (25000000000 / 36811573599) ∧
    -Real.log (25000000000 / 36811573599) ≤ (386936471 / 1000000000) := by
  have h := checkLog_sound (w := (11811573599 / 61811573599)) (n := 12)
    (lo := (38693647 / 100000000)) (hi := (386936471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36811573599 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36811573599 / 25000000000) = 1/(25000000000 / 36811573599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (38693647 / 100000000) (386936471 / 1000000000) (Real.log (36811573599 / 25000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (36811573599 / 25000000000) = -Real.log (25000000000 / 36811573599) := by
    rw [show ((36811573599 / 25000000000) : ℝ) = ((25000000000 / 36811573599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (19379727 / 50000000) ≤ -Real.log (100000000000 / 147343224589) ∧
    -Real.log (100000000000 / 147343224589) ≤ (387594541 / 1000000000) := by
  have h := checkLog_sound (w := (47343224589 / 247343224589)) (n := 12)
    (lo := (19379727 / 50000000)) (hi := (387594541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147343224589 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147343224589 / 100000000000) = 1/(100000000000 / 147343224589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (19379727 / 50000000) (387594541 / 1000000000) (Real.log (147343224589 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (147343224589 / 100000000000) = -Real.log (100000000000 / 147343224589) := by
    rw [show ((147343224589 / 100000000000) : ℝ) = ((100000000000 / 147343224589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (37324617 / 1000000000) ≤ -Real.log (963363360351 / 1000000000000) ∧
    -Real.log (963363360351 / 1000000000000) ≤ (18662309 / 500000000) := by
  have h := checkLog_sound (w := (36636639649 / 1963363360351)) (n := 12)
    (lo := (37324617 / 1000000000)) (hi := (18662309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 963363360351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 963363360351) = 1/(963363360351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-18662309 / 500000000) (-37324617 / 1000000000) (Real.log (963363360351 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (18599381 / 500000000) ≤ -Real.log (9634846119 / 10000000000) ∧
    -Real.log (9634846119 / 10000000000) ≤ (37198763 / 1000000000) := by
  have h := checkLog_sound (w := (365153881 / 19634846119)) (n := 12)
    (lo := (18599381 / 500000000)) (hi := (37198763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9634846119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9634846119) = 1/(9634846119 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-37198763 / 1000000000) (-18599381 / 500000000) (Real.log (9634846119 / 10000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell209
