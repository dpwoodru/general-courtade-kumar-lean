import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell006
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

theorem reflection_log_1_neg : (226419429 / 1000000000) ≤ -Real.log (5120 / 6421) ∧
    -Real.log (5120 / 6421) ≤ (22641943 / 100000000) := by
  have h := checkLog_sound (w := (1301 / 11541)) (n := 12)
    (lo := (226419429 / 1000000000)) (hi := (22641943 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6421 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6421 / 5120) = 1/(5120 / 6421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (226419429 / 1000000000) (22641943 / 100000000) (Real.log (6421 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6421 / 5120) = -Real.log (5120 / 6421) := by
    rw [show ((6421 / 5120) : ℝ) = ((5120 / 6421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (29316583 / 100000000) ≤ -Real.log (3819 / 5120) ∧
    -Real.log (3819 / 5120) ≤ (293165831 / 1000000000) := by
  have h := checkLog_sound (w := (1301 / 8939)) (n := 12)
    (lo := (29316583 / 100000000)) (hi := (293165831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3819) = 1/(3819 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-293165831 / 1000000000) (-29316583 / 100000000) (Real.log (3819 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (225952103 / 1000000000) ≤ -Real.log (2560 / 3209) ∧
    -Real.log (2560 / 3209) ≤ (28244013 / 125000000) := by
  have h := checkLog_sound (w := (649 / 5769)) (n := 12)
    (lo := (225952103 / 1000000000)) (hi := (28244013 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3209 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3209 / 2560) = 1/(2560 / 3209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (225952103 / 1000000000) (28244013 / 125000000) (Real.log (3209 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3209 / 2560) = -Real.log (2560 / 3209) := by
    rw [show ((3209 / 2560) : ℝ) = ((2560 / 3209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (292380593 / 1000000000) ≤ -Real.log (1911 / 2560) ∧
    -Real.log (1911 / 2560) ≤ (146190297 / 500000000) := by
  have h := checkLog_sound (w := (649 / 4471)) (n := 12)
    (lo := (292380593 / 1000000000)) (hi := (146190297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1911) = 1/(1911 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-146190297 / 500000000) (-292380593 / 1000000000) (Real.log (1911 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (165306789 / 1000000000) ≤ -Real.log (200000 / 235951) ∧
    -Real.log (200000 / 235951) ≤ (16530679 / 100000000) := by
  have h := checkLog_sound (w := (35951 / 435951)) (n := 12)
    (lo := (165306789 / 1000000000)) (hi := (16530679 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((235951 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(235951 / 200000) = 1/(200000 / 235951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (165306789 / 1000000000) (16530679 / 100000000) (Real.log (235951 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (235951 / 200000) = -Real.log (200000 / 235951) := by
    rw [show ((235951 / 200000) : ℝ) = ((200000 / 235951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (99076101 / 500000000) ≤ -Real.log (164049 / 200000) ∧
    -Real.log (164049 / 200000) ≤ (198152203 / 1000000000) := by
  have h := checkLog_sound (w := (35951 / 364049)) (n := 12)
    (lo := (99076101 / 500000000)) (hi := (198152203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 164049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 164049) = 1/(164049 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-198152203 / 1000000000) (-99076101 / 500000000) (Real.log (164049 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (33132377 / 200000000) ≤ -Real.log (500000 / 590087) ∧
    -Real.log (500000 / 590087) ≤ (82830943 / 500000000) := by
  have h := checkLog_sound (w := (90087 / 1090087)) (n := 12)
    (lo := (33132377 / 200000000)) (hi := (82830943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590087 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590087 / 500000) = 1/(500000 / 590087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (33132377 / 200000000) (82830943 / 500000000) (Real.log (590087 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (590087 / 500000) = -Real.log (500000 / 590087) := by
    rw [show ((590087 / 500000) : ℝ) = ((500000 / 590087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (49665789 / 250000000) ≤ -Real.log (409913 / 500000) ∧
    -Real.log (409913 / 500000) ≤ (198663157 / 1000000000) := by
  have h := checkLog_sound (w := (90087 / 909913)) (n := 12)
    (lo := (49665789 / 250000000)) (hi := (198663157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 409913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 409913) = 1/(409913 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-198663157 / 1000000000) (-49665789 / 250000000) (Real.log (409913 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (120672191 / 1000000000) ≤ -Real.log (200000 / 225651) ∧
    -Real.log (200000 / 225651) ≤ (1885503 / 15625000) := by
  have h := checkLog_sound (w := (25651 / 425651)) (n := 12)
    (lo := (120672191 / 1000000000)) (hi := (1885503 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((225651 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(225651 / 200000) = 1/(200000 / 225651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (120672191 / 1000000000) (1885503 / 15625000) (Real.log (225651 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (225651 / 200000) = -Real.log (200000 / 225651) := by
    rw [show ((225651 / 200000) : ℝ) = ((200000 / 225651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (137258329 / 1000000000) ≤ -Real.log (174349 / 200000) ∧
    -Real.log (174349 / 200000) ≤ (13725833 / 100000000) := by
  have h := checkLog_sound (w := (25651 / 374349)) (n := 12)
    (lo := (137258329 / 1000000000)) (hi := (13725833 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 174349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 174349) = 1/(174349 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-13725833 / 100000000) (-137258329 / 1000000000) (Real.log (174349 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (120941597 / 1000000000) ≤ -Real.log (1000000 / 1128559) ∧
    -Real.log (1000000 / 1128559) ≤ (60470799 / 500000000) := by
  have h := checkLog_sound (w := (128559 / 2128559)) (n := 12)
    (lo := (120941597 / 1000000000)) (hi := (60470799 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1128559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1128559 / 1000000) = 1/(1000000 / 1128559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (120941597 / 1000000000) (60470799 / 500000000) (Real.log (1128559 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1128559 / 1000000) = -Real.log (1000000 / 1128559) := by
    rw [show ((1128559 / 1000000) : ℝ) = ((1000000 / 1128559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (27521423 / 200000000) ≤ -Real.log (871441 / 1000000) ∧
    -Real.log (871441 / 1000000) ≤ (34401779 / 250000000) := by
  have h := checkLog_sound (w := (128559 / 1871441)) (n := 12)
    (lo := (27521423 / 200000000)) (hi := (34401779 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 871441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 871441) = 1/(871441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-34401779 / 250000000) (-27521423 / 200000000) (Real.log (871441 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (64791587 / 125000000) ≤ -Real.log (62500000000 / 104951596023) ∧
    -Real.log (62500000000 / 104951596023) ≤ (518332697 / 1000000000) := by
  have h := checkLog_sound (w := (42451596023 / 167451596023)) (n := 12)
    (lo := (64791587 / 125000000)) (hi := (518332697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((104951596023 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(104951596023 / 62500000000) = 1/(62500000000 / 104951596023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (64791587 / 125000000) (518332697 / 1000000000) (Real.log (104951596023 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (104951596023 / 62500000000) = -Real.log (62500000000 / 104951596023) := by
    rw [show ((104951596023 / 62500000000) : ℝ) = ((62500000000 / 104951596023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (25979263 / 50000000) ≤ -Real.log (20000000000 / 33626603823) ∧
    -Real.log (20000000000 / 33626603823) ≤ (519585261 / 1000000000) := by
  have h := checkLog_sound (w := (13626603823 / 53626603823)) (n := 12)
    (lo := (25979263 / 50000000)) (hi := (519585261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33626603823 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33626603823 / 20000000000) = 1/(20000000000 / 33626603823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (25979263 / 50000000) (519585261 / 1000000000) (Real.log (33626603823 / 20000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (33626603823 / 20000000000) = -Real.log (20000000000 / 33626603823) := by
    rw [show ((33626603823 / 20000000000) : ℝ) = ((20000000000 / 33626603823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (22716187 / 62500000) ≤ -Real.log (250000000000 / 359573968753) ∧
    -Real.log (250000000000 / 359573968753) ≤ (363458993 / 1000000000) := by
  have h := checkLog_sound (w := (109573968753 / 609573968753)) (n := 12)
    (lo := (22716187 / 62500000)) (hi := (363458993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359573968753 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359573968753 / 250000000000) = 1/(250000000000 / 359573968753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (22716187 / 62500000) (363458993 / 1000000000) (Real.log (359573968753 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (359573968753 / 250000000000) = -Real.log (250000000000 / 359573968753) := by
    rw [show ((359573968753 / 250000000000) : ℝ) = ((250000000000 / 359573968753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (364325041 / 1000000000) ≤ -Real.log (62500000000 / 89971378073) ∧
    -Real.log (62500000000 / 89971378073) ≤ (182162521 / 500000000) := by
  have h := checkLog_sound (w := (27471378073 / 152471378073)) (n := 12)
    (lo := (364325041 / 1000000000)) (hi := (182162521 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89971378073 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89971378073 / 62500000000) = 1/(62500000000 / 89971378073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (364325041 / 1000000000) (182162521 / 500000000) (Real.log (89971378073 / 62500000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (89971378073 / 62500000000) = -Real.log (62500000000 / 89971378073) := by
    rw [show ((89971378073 / 62500000000) : ℝ) = ((62500000000 / 89971378073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (6448263 / 25000000) ≤ -Real.log (100000000000 / 129424889159) ∧
    -Real.log (100000000000 / 129424889159) ≤ (257930521 / 1000000000) := by
  have h := checkLog_sound (w := (29424889159 / 229424889159)) (n := 12)
    (lo := (6448263 / 25000000)) (hi := (257930521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((129424889159 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(129424889159 / 100000000000) = 1/(100000000000 / 129424889159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (6448263 / 25000000) (257930521 / 1000000000) (Real.log (129424889159 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (129424889159 / 100000000000) = -Real.log (100000000000 / 129424889159) := by
    rw [show ((129424889159 / 100000000000) : ℝ) = ((100000000000 / 129424889159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (258548713 / 1000000000) ≤ -Real.log (62500000000 / 80940577159) ∧
    -Real.log (62500000000 / 80940577159) ≤ (129274357 / 500000000) := by
  have h := checkLog_sound (w := (18440577159 / 143440577159)) (n := 12)
    (lo := (258548713 / 1000000000)) (hi := (129274357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80940577159 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80940577159 / 62500000000) = 1/(62500000000 / 80940577159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (258548713 / 1000000000) (129274357 / 500000000) (Real.log (80940577159 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (80940577159 / 62500000000) = -Real.log (62500000000 / 80940577159) := by
    rw [show ((80940577159 / 62500000000) : ℝ) = ((62500000000 / 80940577159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (16665517 / 1000000000) ≤ -Real.log (983472583519 / 1000000000000) ∧
    -Real.log (983472583519 / 1000000000000) ≤ (8332759 / 500000000) := by
  have h := checkLog_sound (w := (16527416481 / 1983472583519)) (n := 12)
    (lo := (16665517 / 1000000000)) (hi := (8332759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983472583519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983472583519) = 1/(983472583519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-8332759 / 500000000) (-16665517 / 1000000000) (Real.log (983472583519 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (16586137 / 1000000000) ≤ -Real.log (39342026199 / 40000000000) ∧
    -Real.log (39342026199 / 40000000000) ≤ (8293069 / 500000000) := by
  have h := checkLog_sound (w := (657973801 / 79342026199)) (n := 12)
    (lo := (16586137 / 1000000000)) (hi := (8293069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39342026199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39342026199) = 1/(39342026199 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-8293069 / 500000000) (-16586137 / 1000000000) (Real.log (39342026199 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell006
