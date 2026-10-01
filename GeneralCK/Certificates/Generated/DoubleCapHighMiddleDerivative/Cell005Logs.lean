import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell005
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

theorem reflection_log_1_neg : (225952103 / 1000000000) ≤ -Real.log (2560 / 3209) ∧
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


theorem reflection_log_1 : Bounds (225952103 / 1000000000) (28244013 / 125000000) (Real.log (3209 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3209 / 2560) = -Real.log (2560 / 3209) := by
    rw [show ((3209 / 2560) : ℝ) = ((2560 / 3209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (292380593 / 1000000000) ≤ -Real.log (1911 / 2560) ∧
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


theorem reflection_log_2 : Bounds (-146190297 / 500000000) (-292380593 / 1000000000) (Real.log (1911 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (225484559 / 1000000000) ≤ -Real.log (1024 / 1283) ∧
    -Real.log (1024 / 1283) ≤ (2818557 / 12500000) := by
  have h := checkLog_sound (w := (259 / 2307)) (n := 12)
    (lo := (225484559 / 1000000000)) (hi := (2818557 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1283 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1283 / 1024) = 1/(1024 / 1283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (225484559 / 1000000000) (2818557 / 12500000) (Real.log (1283 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1283 / 1024) = -Real.log (1024 / 1283) := by
    rw [show ((1283 / 1024) : ℝ) = ((1024 / 1283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (291595971 / 1000000000) ≤ -Real.log (765 / 1024) ∧
    -Real.log (765 / 1024) ≤ (72898993 / 250000000) := by
  have h := checkLog_sound (w := (259 / 1789)) (n := 12)
    (lo := (291595971 / 1000000000)) (hi := (72898993 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 765) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 765) = 1/(765 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-72898993 / 250000000) (-291595971 / 1000000000) (Real.log (765 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (10309579 / 62500000) ≤ -Real.log (500000 / 589669) ∧
    -Real.log (500000 / 589669) ≤ (32990653 / 200000000) := by
  have h := checkLog_sound (w := (89669 / 1089669)) (n := 12)
    (lo := (10309579 / 62500000)) (hi := (32990653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589669 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589669 / 500000) = 1/(500000 / 589669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (10309579 / 62500000) (32990653 / 200000000) (Real.log (589669 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (589669 / 500000) = -Real.log (500000 / 589669) := by
    rw [show ((589669 / 500000) : ℝ) = ((500000 / 589669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (197643947 / 1000000000) ≤ -Real.log (410331 / 500000) ∧
    -Real.log (410331 / 500000) ≤ (49410987 / 250000000) := by
  have h := checkLog_sound (w := (89669 / 910331)) (n := 12)
    (lo := (197643947 / 1000000000)) (hi := (49410987 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 410331) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 410331) = 1/(410331 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-49410987 / 250000000) (-197643947 / 1000000000) (Real.log (410331 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (165307637 / 1000000000) ≤ -Real.log (250000 / 294939) ∧
    -Real.log (250000 / 294939) ≤ (82653819 / 500000000) := by
  have h := checkLog_sound (w := (44939 / 544939)) (n := 12)
    (lo := (165307637 / 1000000000)) (hi := (82653819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294939 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294939 / 250000) = 1/(250000 / 294939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (165307637 / 1000000000) (82653819 / 500000000) (Real.log (294939 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (294939 / 250000) = -Real.log (250000 / 294939) := by
    rw [show ((294939 / 250000) : ℝ) = ((250000 / 294939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (99076711 / 500000000) ≤ -Real.log (205061 / 250000) ∧
    -Real.log (205061 / 250000) ≤ (198153423 / 1000000000) := by
  have h := checkLog_sound (w := (44939 / 455061)) (n := 12)
    (lo := (99076711 / 500000000)) (hi := (198153423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 205061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 205061) = 1/(205061 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-198153423 / 1000000000) (-99076711 / 500000000) (Real.log (205061 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (15050339 / 125000000) ≤ -Real.log (1000000 / 1127951) ∧
    -Real.log (1000000 / 1127951) ≤ (120402713 / 1000000000) := by
  have h := checkLog_sound (w := (127951 / 2127951)) (n := 12)
    (lo := (15050339 / 125000000)) (hi := (120402713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1127951 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1127951 / 1000000) = 1/(1000000 / 1127951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (15050339 / 125000000) (120402713 / 1000000000) (Real.log (1127951 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1127951 / 1000000) = -Real.log (1000000 / 1127951) := by
    rw [show ((1127951 / 1000000) : ℝ) = ((1000000 / 1127951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (136909663 / 1000000000) ≤ -Real.log (872049 / 1000000) ∧
    -Real.log (872049 / 1000000) ≤ (4278427 / 31250000) := by
  have h := checkLog_sound (w := (127951 / 1872049)) (n := 12)
    (lo := (136909663 / 1000000000)) (hi := (4278427 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 872049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 872049) = 1/(872049 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4278427 / 31250000) (-136909663 / 1000000000) (Real.log (872049 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (120673077 / 1000000000) ≤ -Real.log (15625 / 17629) ∧
    -Real.log (15625 / 17629) ≤ (60336539 / 500000000) := by
  have h := checkLog_sound (w := (1002 / 16627)) (n := 12)
    (lo := (120673077 / 1000000000)) (hi := (60336539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17629 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17629 / 15625) = 1/(15625 / 17629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (120673077 / 1000000000) (60336539 / 500000000) (Real.log (17629 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (17629 / 15625) = -Real.log (15625 / 17629) := by
    rw [show ((17629 / 15625) : ℝ) = ((15625 / 17629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (34314869 / 250000000) ≤ -Real.log (13621 / 15625) ∧
    -Real.log (13621 / 15625) ≤ (137259477 / 1000000000) := by
  have h := checkLog_sound (w := (1002 / 14623)) (n := 12)
    (lo := (34314869 / 250000000)) (hi := (137259477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 13621) = 1/(13621 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-137259477 / 1000000000) (-34314869 / 250000000) (Real.log (13621 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (51708053 / 100000000) ≤ -Real.log (500000000000 / 838562091503) ∧
    -Real.log (500000000000 / 838562091503) ≤ (517080531 / 1000000000) := by
  have h := checkLog_sound (w := (338562091503 / 1338562091503)) (n := 12)
    (lo := (51708053 / 100000000)) (hi := (517080531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((838562091503 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(838562091503 / 500000000000) = 1/(500000000000 / 838562091503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (51708053 / 100000000) (517080531 / 1000000000) (Real.log (838562091503 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (838562091503 / 500000000000) = -Real.log (500000000000 / 838562091503) := by
    rw [show ((838562091503 / 500000000000) : ℝ) = ((500000000000 / 838562091503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (64791587 / 125000000) ≤ -Real.log (100000000000 / 167922553637) ∧
    -Real.log (100000000000 / 167922553637) ≤ (518332697 / 1000000000) := by
  have h := checkLog_sound (w := (67922553637 / 267922553637)) (n := 12)
    (lo := (64791587 / 125000000)) (hi := (518332697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((167922553637 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(167922553637 / 100000000000) = 1/(100000000000 / 167922553637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (64791587 / 125000000) (518332697 / 1000000000) (Real.log (167922553637 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (167922553637 / 100000000000) = -Real.log (100000000000 / 167922553637) := by
    rw [show ((167922553637 / 100000000000) : ℝ) = ((100000000000 / 167922553637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (362597211 / 1000000000) ≤ -Real.log (100000000000 / 143705691259) ∧
    -Real.log (100000000000 / 143705691259) ≤ (90649303 / 250000000) := by
  have h := checkLog_sound (w := (43705691259 / 243705691259)) (n := 12)
    (lo := (362597211 / 1000000000)) (hi := (90649303 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143705691259 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143705691259 / 100000000000) = 1/(100000000000 / 143705691259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (362597211 / 1000000000) (90649303 / 250000000) (Real.log (143705691259 / 100000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (143705691259 / 100000000000) = -Real.log (100000000000 / 143705691259) := by
    rw [show ((143705691259 / 100000000000) : ℝ) = ((100000000000 / 143705691259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (363461059 / 1000000000) ≤ -Real.log (50000000000 / 71914942383) ∧
    -Real.log (50000000000 / 71914942383) ≤ (18173053 / 50000000) := by
  have h := checkLog_sound (w := (21914942383 / 121914942383)) (n := 12)
    (lo := (363461059 / 1000000000)) (hi := (18173053 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71914942383 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71914942383 / 50000000000) = 1/(50000000000 / 71914942383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (363461059 / 1000000000) (18173053 / 50000000) (Real.log (71914942383 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (71914942383 / 50000000000) = -Real.log (50000000000 / 71914942383) := by
    rw [show ((71914942383 / 50000000000) : ℝ) = ((50000000000 / 71914942383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (32164047 / 125000000) ≤ -Real.log (250000000000 / 323362276661) ∧
    -Real.log (250000000000 / 323362276661) ≤ (257312377 / 1000000000) := by
  have h := checkLog_sound (w := (73362276661 / 573362276661)) (n := 12)
    (lo := (32164047 / 125000000)) (hi := (257312377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((323362276661 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(323362276661 / 250000000000) = 1/(250000000000 / 323362276661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (32164047 / 125000000) (257312377 / 1000000000) (Real.log (323362276661 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (323362276661 / 250000000000) = -Real.log (250000000000 / 323362276661) := by
    rw [show ((323362276661 / 250000000000) : ℝ) = ((250000000000 / 323362276661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (257932553 / 1000000000) ≤ -Real.log (125000000000 / 161781440423) ∧
    -Real.log (125000000000 / 161781440423) ≤ (128966277 / 500000000) := by
  have h := checkLog_sound (w := (36781440423 / 286781440423)) (n := 12)
    (lo := (257932553 / 1000000000)) (hi := (128966277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((161781440423 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(161781440423 / 125000000000) = 1/(125000000000 / 161781440423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (257932553 / 1000000000) (128966277 / 500000000) (Real.log (161781440423 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (161781440423 / 125000000000) = -Real.log (125000000000 / 161781440423) := by
    rw [show ((161781440423 / 125000000000) : ℝ) = ((125000000000 / 161781440423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (8293199 / 500000000) ≤ -Real.log (240124609 / 244140625) ∧
    -Real.log (240124609 / 244140625) ≤ (16586399 / 1000000000) := by
  have h := checkLog_sound (w := (2008008 / 242132617)) (n := 12)
    (lo := (8293199 / 500000000)) (hi := (16586399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 240124609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 240124609) = 1/(240124609 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-16586399 / 1000000000) (-8293199 / 500000000) (Real.log (240124609 / 244140625)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (16506951 / 1000000000) ≤ -Real.log (983628541599 / 1000000000000) ∧
    -Real.log (983628541599 / 1000000000000) ≤ (2063369 / 125000000) := by
  have h := checkLog_sound (w := (16371458401 / 1983628541599)) (n := 12)
    (lo := (16506951 / 1000000000)) (hi := (2063369 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 983628541599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 983628541599) = 1/(983628541599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2063369 / 125000000) (-16506951 / 1000000000) (Real.log (983628541599 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell005
