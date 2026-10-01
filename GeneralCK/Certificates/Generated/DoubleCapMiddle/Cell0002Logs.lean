import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0002
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

theorem reflection_log_1_neg : (56781909 / 125000000) ≤ -Real.log (40 / 63) ∧
    -Real.log (40 / 63) ≤ (454255273 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 103)) (n := 12)
    (lo := (56781909 / 125000000)) (hi := (454255273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63 / 40) = 1/(40 / 63) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (56781909 / 125000000) (454255273 / 1000000000) (Real.log (63 / 40)) := by
  have h := reflection_log_1_neg
  have he : Real.log (63 / 40) = -Real.log (40 / 63) := by
    rw [show ((63 / 40) : ℝ) = ((40 / 63) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (855666109 / 1000000000) ≤ -Real.log (17 / 40) ∧
    -Real.log (17 / 40) ≤ (855666111 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 37)) (n := 12)
    (lo := (162518929 / 1000000000)) (hi := (16251893 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 17) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20 / 17) = 1/(17 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-855666111 / 1000000000) (-855666109 / 1000000000) (Real.log (17 / 40)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (223143551 / 500000000) ≤ -Real.log (16 / 25) ∧
    -Real.log (16 / 25) ≤ (446287103 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 41)) (n := 12)
    (lo := (223143551 / 500000000)) (hi := (446287103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 16) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25 / 16) = 1/(16 / 25) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (223143551 / 500000000) (446287103 / 1000000000) (Real.log (25 / 16)) := by
  have h := reflection_log_3_neg
  have he : Real.log (25 / 16) = -Real.log (16 / 25) := by
    rw [show ((25 / 16) : ℝ) = ((16 / 25) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (206669643 / 250000000) ≤ -Real.log (7 / 16) ∧
    -Real.log (7 / 16) ≤ (413339287 / 500000000) := by
  have h := checkLog_sound (w := (1 / 15)) (n := 12)
    (lo := (521607 / 3906250)) (hi := (133531393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8 / 7) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(8 / 7) = 1/(7 / 16) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-413339287 / 500000000) (-206669643 / 250000000) (Real.log (7 / 16)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (69880971 / 500000000) ≤ -Real.log (20 / 23) ∧
    -Real.log (20 / 23) ≤ (139761943 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 43)) (n := 12)
    (lo := (69880971 / 500000000)) (hi := (139761943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23 / 20) = 1/(20 / 23) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (69880971 / 500000000) (139761943 / 1000000000) (Real.log (23 / 20)) := by
  have h := reflection_log_5_neg
  have he : Real.log (23 / 20) = -Real.log (20 / 23) := by
    rw [show ((23 / 20) : ℝ) = ((20 / 23) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (162518929 / 1000000000) ≤ -Real.log (17 / 20) ∧
    -Real.log (17 / 20) ≤ (16251893 / 100000000) := by
  have h := checkLog_sound (w := (3 / 37)) (n := 12)
    (lo := (162518929 / 1000000000)) (hi := (16251893 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 17) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20 / 17) = 1/(17 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-16251893 / 100000000) (-162518929 / 1000000000) (Real.log (17 / 20)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23556607 / 200000000) ≤ -Real.log (8 / 9) ∧
    -Real.log (8 / 9) ≤ (29445759 / 250000000) := by
  have h := checkLog_sound (w := (1 / 17)) (n := 12)
    (lo := (23556607 / 200000000)) (hi := (29445759 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9 / 8) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9 / 8) = 1/(8 / 9) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (23556607 / 200000000) (29445759 / 250000000) (Real.log (9 / 8)) := by
  have h := reflection_log_7_neg
  have he : Real.log (9 / 8) = -Real.log (8 / 9) := by
    rw [show ((9 / 8) : ℝ) = ((8 / 9) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (521607 / 3906250) ≤ -Real.log (7 / 8) ∧
    -Real.log (7 / 8) ≤ (133531393 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 15)) (n := 12)
    (lo := (521607 / 3906250)) (hi := (133531393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8 / 7) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8 / 7) = 1/(7 / 8) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-133531393 / 1000000000) (-521607 / 3906250) (Real.log (7 / 8)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (289337641 / 500000000) ≤ -Real.log (500000 / 891837) ∧
    -Real.log (500000 / 891837) ≤ (578675283 / 1000000000) := by
  have h := checkLog_sound (w := (391837 / 1391837)) (n := 12)
    (lo := (289337641 / 500000000)) (hi := (578675283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((891837 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(891837 / 500000) = 1/(500000 / 891837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (289337641 / 500000000) (578675283 / 1000000000) (Real.log (891837 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (891837 / 500000) = -Real.log (500000 / 891837) := by
    rw [show ((891837 / 500000) : ℝ) = ((500000 / 891837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (382742187 / 250000000) ≤ -Real.log (108163 / 500000) ∧
    -Real.log (108163 / 500000) ≤ (1530968751 / 1000000000) := by
  have h := checkLog_sound (w := (16837 / 233163)) (n := 12)
    (lo := (36168597 / 250000000)) (hi := (144674389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 108163) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 108163) = 1/(108163 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1530968751 / 1000000000) (-382742187 / 250000000) (Real.log (108163 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (579592629 / 1000000000) ≤ -Real.log (1000000 / 1785311) ∧
    -Real.log (1000000 / 1785311) ≤ (57959263 / 100000000) := by
  have h := checkLog_sound (w := (785311 / 2785311)) (n := 12)
    (lo := (579592629 / 1000000000)) (hi := (57959263 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1785311 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1785311 / 1000000) = 1/(1000000 / 1785311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (579592629 / 1000000000) (57959263 / 100000000) (Real.log (1785311 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1785311 / 1000000) = -Real.log (1000000 / 1785311) := by
    rw [show ((1785311 / 1000000) : ℝ) = ((1000000 / 1785311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (192320601 / 125000000) ≤ -Real.log (214689 / 1000000) ∧
    -Real.log (214689 / 1000000) ≤ (1538564811 / 1000000000) := by
  have h := checkLog_sound (w := (35311 / 464689)) (n := 12)
    (lo := (9516903 / 62500000)) (hi := (152270449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 214689) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 214689) = 1/(214689 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1538564811 / 1000000000) (-192320601 / 125000000) (Real.log (214689 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (105829313 / 200000000) ≤ -Real.log (1000000 / 1697483) ∧
    -Real.log (1000000 / 1697483) ≤ (264573283 / 500000000) := by
  have h := checkLog_sound (w := (697483 / 2697483)) (n := 12)
    (lo := (105829313 / 200000000)) (hi := (264573283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1697483 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1697483 / 1000000) = 1/(1000000 / 1697483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (105829313 / 200000000) (264573283 / 500000000) (Real.log (1697483 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1697483 / 1000000) = -Real.log (1000000 / 1697483) := by
    rw [show ((1697483 / 1000000) : ℝ) = ((1000000 / 1697483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (298904451 / 250000000) ≤ -Real.log (302517 / 1000000) ∧
    -Real.log (302517 / 1000000) ≤ (597808903 / 500000000) := by
  have h := checkLog_sound (w := (197483 / 802517)) (n := 12)
    (lo := (15702207 / 31250000)) (hi := (803953 / 1600000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 302517) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 302517) = 1/(302517 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-597808903 / 500000000) (-298904451 / 250000000) (Real.log (302517 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (266850879 / 500000000) ≤ -Real.log (1000000 / 1705233) ∧
    -Real.log (1000000 / 1705233) ≤ (533701759 / 1000000000) := by
  have h := checkLog_sound (w := (705233 / 2705233)) (n := 12)
    (lo := (266850879 / 500000000)) (hi := (533701759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1705233 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1705233 / 1000000) = 1/(1000000 / 1705233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (266850879 / 500000000) (533701759 / 1000000000) (Real.log (1705233 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1705233 / 1000000) = -Real.log (1000000 / 1705233) := by
    rw [show ((1705233 / 1000000) : ℝ) = ((1000000 / 1705233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (76348129 / 62500000) ≤ -Real.log (294767 / 1000000) ∧
    -Real.log (294767 / 1000000) ≤ (610785033 / 500000000) := by
  have h := checkLog_sound (w := (205233 / 794767)) (n := 12)
    (lo := (132105721 / 250000000)) (hi := (105684577 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 294767) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 294767) = 1/(294767 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-610785033 / 500000000) (-76348129 / 62500000) (Real.log (294767 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (210964403 / 100000000) ≤ -Real.log (31250000000 / 257665803001) ∧
    -Real.log (31250000000 / 257665803001) ≤ (1054822017 / 500000000) := by
  have h := checkLog_sound (w := (7665803001 / 507665803001)) (n := 12)
    (lo := (3020249 / 100000000)) (hi := (30202491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((257665803001 / 250000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(257665803001 / 250000000000) = 1/(31250000000 / 257665803001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (210964403 / 100000000) (1054822017 / 500000000) (Real.log (257665803001 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (257665803001 / 31250000000) = -Real.log (31250000000 / 257665803001) := by
    rw [show ((257665803001 / 31250000000) : ℝ) = ((31250000000 / 257665803001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2118157437 / 1000000000) ≤ -Real.log (50000000000 / 415790049793) ∧
    -Real.log (50000000000 / 415790049793) ≤ (2118157441 / 1000000000) := by
  have h := checkLog_sound (w := (15790049793 / 815790049793)) (n := 12)
    (lo := (38715897 / 1000000000)) (hi := (19357949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((415790049793 / 400000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(415790049793 / 400000000000) = 1/(50000000000 / 415790049793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2118157437 / 1000000000) (2118157441 / 1000000000) (Real.log (415790049793 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (415790049793 / 50000000000) = -Real.log (50000000000 / 415790049793) := by
    rw [show ((415790049793 / 50000000000) : ℝ) = ((50000000000 / 415790049793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1724764369 / 1000000000) ≤ -Real.log (500000000000 / 2805599354747) ∧
    -Real.log (500000000000 / 2805599354747) ≤ (431191093 / 250000000) := by
  have h := checkLog_sound (w := (805599354747 / 4805599354747)) (n := 12)
    (lo := (338470009 / 1000000000)) (hi := (33847001 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2805599354747 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2805599354747 / 2000000000000) = 1/(500000000000 / 2805599354747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1724764369 / 1000000000) (431191093 / 250000000) (Real.log (2805599354747 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2805599354747 / 500000000000) = -Real.log (500000000000 / 2805599354747) := by
    rw [show ((2805599354747 / 500000000000) : ℝ) = ((500000000000 / 2805599354747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (877635911 / 500000000) ≤ -Real.log (250000000000 / 1446255008193) ∧
    -Real.log (250000000000 / 1446255008193) ≤ (70210873 / 40000000) := by
  have h := checkLog_sound (w := (446255008193 / 2446255008193)) (n := 12)
    (lo := (184488731 / 500000000)) (hi := (368977463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1446255008193 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1446255008193 / 1000000000000) = 1/(250000000000 / 1446255008193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (877635911 / 500000000) (70210873 / 40000000) (Real.log (1446255008193 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1446255008193 / 250000000000) = -Real.log (250000000000 / 1446255008193) := by
    rw [show ((1446255008193 / 250000000000) : ℝ) = ((250000000000 / 1446255008193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0002
