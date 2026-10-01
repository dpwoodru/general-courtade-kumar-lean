import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0083
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

theorem reflection_log_1_neg : (347571129 / 1000000000) ≤ -Real.log (320 / 453) ∧
    -Real.log (320 / 453) ≤ (34757113 / 100000000) := by
  have h := checkLog_sound (w := (133 / 773)) (n := 12)
    (lo := (347571129 / 1000000000)) (hi := (34757113 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((453 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(453 / 320) = 1/(320 / 453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (347571129 / 1000000000) (34757113 / 100000000) (Real.log (453 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (453 / 320) = -Real.log (320 / 453) := by
    rw [show ((453 / 320) : ℝ) = ((320 / 453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (268606189 / 500000000) ≤ -Real.log (187 / 320) ∧
    -Real.log (187 / 320) ≤ (537212379 / 1000000000) := by
  have h := checkLog_sound (w := (133 / 507)) (n := 12)
    (lo := (268606189 / 500000000)) (hi := (537212379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 187) = 1/(187 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-537212379 / 1000000000) (-268606189 / 500000000) (Real.log (187 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (86685743 / 250000000) ≤ -Real.log (2560 / 3621) ∧
    -Real.log (2560 / 3621) ≤ (346742973 / 1000000000) := by
  have h := checkLog_sound (w := (1061 / 6181)) (n := 12)
    (lo := (86685743 / 250000000)) (hi := (346742973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3621 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3621 / 2560) = 1/(2560 / 3621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (86685743 / 250000000) (346742973 / 1000000000) (Real.log (3621 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3621 / 2560) = -Real.log (2560 / 3621) := by
    rw [show ((3621 / 2560) : ℝ) = ((2560 / 3621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (535209039 / 1000000000) ≤ -Real.log (1499 / 2560) ∧
    -Real.log (1499 / 2560) ≤ (6690113 / 12500000) := by
  have h := checkLog_sound (w := (1061 / 4059)) (n := 12)
    (lo := (535209039 / 1000000000)) (hi := (6690113 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1499) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1499) = 1/(1499 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6690113 / 12500000) (-535209039 / 1000000000) (Real.log (1499 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (604998793 / 1000000000) ≤ -Real.log (160 / 293) ∧
    -Real.log (160 / 293) ≤ (302499397 / 500000000) := by
  have h := checkLog_sound (w := (133 / 453)) (n := 12)
    (lo := (604998793 / 1000000000)) (hi := (302499397 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293 / 160) = 1/(160 / 293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (604998793 / 1000000000) (302499397 / 500000000) (Real.log (293 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (293 / 160) = -Real.log (160 / 293) := by
    rw [show ((293 / 160) : ℝ) = ((160 / 293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (444834237 / 250000000) ≤ -Real.log (27 / 160) ∧
    -Real.log (27 / 160) ≤ (1779336951 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(40 / 27) = 1/(27 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1779336951 / 1000000000) (-444834237 / 250000000) (Real.log (27 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (60371811 / 100000000) ≤ -Real.log (1280 / 2341) ∧
    -Real.log (1280 / 2341) ≤ (603718111 / 1000000000) := by
  have h := checkLog_sound (w := (1061 / 3621)) (n := 12)
    (lo := (60371811 / 100000000)) (hi := (603718111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2341 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2341 / 1280) = 1/(1280 / 2341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (60371811 / 100000000) (603718111 / 1000000000) (Real.log (2341 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2341 / 1280) = -Real.log (1280 / 2341) := by
    rw [show ((2341 / 1280) : ℝ) = ((1280 / 2341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (14124349 / 8000000) ≤ -Real.log (219 / 1280) ∧
    -Real.log (219 / 1280) ≤ (441385907 / 250000000) := by
  have h := checkLog_sound (w := (101 / 539)) (n := 12)
    (lo := (75849853 / 200000000)) (hi := (189624633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 219) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(320 / 219) = 1/(219 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-441385907 / 250000000) (-14124349 / 8000000) (Real.log (219 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (476901037 / 1000000000) ≤ -Real.log (500000 / 805537) ∧
    -Real.log (500000 / 805537) ≤ (238450519 / 500000000) := by
  have h := checkLog_sound (w := (305537 / 1305537)) (n := 12)
    (lo := (476901037 / 1000000000)) (hi := (238450519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((805537 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(805537 / 500000) = 1/(500000 / 805537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (476901037 / 1000000000) (238450519 / 500000000) (Real.log (805537 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (805537 / 500000) = -Real.log (500000 / 805537) := by
    rw [show ((805537 / 500000) : ℝ) = ((500000 / 805537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (118045773 / 125000000) ≤ -Real.log (194463 / 500000) ∧
    -Real.log (194463 / 500000) ≤ (472183093 / 500000000) := by
  have h := checkLog_sound (w := (55537 / 444463)) (n := 12)
    (lo := (62804751 / 250000000)) (hi := (50243801 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 194463) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 194463) = 1/(194463 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-472183093 / 500000000) (-118045773 / 125000000) (Real.log (194463 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (478115017 / 1000000000) ≤ -Real.log (1000000 / 1613031) ∧
    -Real.log (1000000 / 1613031) ≤ (239057509 / 500000000) := by
  have h := checkLog_sound (w := (613031 / 2613031)) (n := 12)
    (lo := (478115017 / 1000000000)) (hi := (239057509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1613031 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1613031 / 1000000) = 1/(1000000 / 1613031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (478115017 / 1000000000) (239057509 / 500000000) (Real.log (1613031 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1613031 / 1000000) = -Real.log (1000000 / 1613031) := by
    rw [show ((1613031 / 1000000) : ℝ) = ((1000000 / 1613031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (949410691 / 1000000000) ≤ -Real.log (386969 / 1000000) ∧
    -Real.log (386969 / 1000000) ≤ (949410693 / 1000000000) := by
  have h := checkLog_sound (w := (113031 / 886969)) (n := 12)
    (lo := (256263511 / 1000000000)) (hi := (32032939 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 386969) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 386969) = 1/(386969 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-949410693 / 1000000000) (-949410691 / 1000000000) (Real.log (386969 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (393034163 / 1000000000) ≤ -Real.log (1000000 / 1481469) ∧
    -Real.log (1000000 / 1481469) ≤ (98258541 / 250000000) := by
  have h := checkLog_sound (w := (481469 / 2481469)) (n := 12)
    (lo := (393034163 / 1000000000)) (hi := (98258541 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1481469 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1481469 / 1000000) = 1/(1000000 / 1481469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (393034163 / 1000000000) (98258541 / 250000000) (Real.log (1481469 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1481469 / 1000000) = -Real.log (1000000 / 1481469) := by
    rw [show ((1481469 / 1000000) : ℝ) = ((1000000 / 1481469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (131351093 / 200000000) ≤ -Real.log (518531 / 1000000) ∧
    -Real.log (518531 / 1000000) ≤ (328377733 / 500000000) := by
  have h := checkLog_sound (w := (481469 / 1518531)) (n := 12)
    (lo := (131351093 / 200000000)) (hi := (328377733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 518531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 518531) = 1/(518531 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-328377733 / 500000000) (-131351093 / 200000000) (Real.log (518531 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (39430911 / 100000000) ≤ -Real.log (1000000 / 1483359) ∧
    -Real.log (1000000 / 1483359) ≤ (394309111 / 1000000000) := by
  have h := checkLog_sound (w := (483359 / 2483359)) (n := 12)
    (lo := (39430911 / 100000000)) (hi := (394309111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1483359 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1483359 / 1000000) = 1/(1000000 / 1483359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (39430911 / 100000000) (394309111 / 1000000000) (Real.log (1483359 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1483359 / 1000000) = -Real.log (1000000 / 1483359) := by
    rw [show ((1483359 / 1000000) : ℝ) = ((1000000 / 1483359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (165101759 / 250000000) ≤ -Real.log (516641 / 1000000) ∧
    -Real.log (516641 / 1000000) ≤ (660407037 / 1000000000) := by
  have h := checkLog_sound (w := (483359 / 1516641)) (n := 12)
    (lo := (165101759 / 250000000)) (hi := (660407037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 516641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 516641) = 1/(516641 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-660407037 / 1000000000) (-165101759 / 250000000) (Real.log (516641 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1421267221 / 1000000000) ≤ -Real.log (31250000000 / 129448950443) ∧
    -Real.log (31250000000 / 129448950443) ≤ (177658403 / 125000000) := by
  have h := checkLog_sound (w := (4448950443 / 254448950443)) (n := 12)
    (lo := (34972861 / 1000000000)) (hi := (17486431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((129448950443 / 125000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(129448950443 / 125000000000) = 1/(31250000000 / 129448950443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1421267221 / 1000000000) (177658403 / 125000000) (Real.log (129448950443 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (129448950443 / 31250000000) = -Real.log (31250000000 / 129448950443) := by
    rw [show ((129448950443 / 31250000000) : ℝ) = ((31250000000 / 129448950443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1427525709 / 1000000000) ≤ -Real.log (125000000000 / 521046582543) ∧
    -Real.log (125000000000 / 521046582543) ≤ (89220357 / 62500000) := by
  have h := checkLog_sound (w := (21046582543 / 1021046582543)) (n := 12)
    (lo := (41231349 / 1000000000)) (hi := (824627 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((521046582543 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(521046582543 / 500000000000) = 1/(125000000000 / 521046582543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1427525709 / 1000000000) (89220357 / 62500000) (Real.log (521046582543 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (521046582543 / 125000000000) = -Real.log (125000000000 / 521046582543) := by
    rw [show ((521046582543 / 125000000000) : ℝ) = ((125000000000 / 521046582543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1049789627 / 1000000000) ≤ -Real.log (500000000000 / 1428525006219) ∧
    -Real.log (500000000000 / 1428525006219) ≤ (1049789629 / 1000000000) := by
  have h := checkLog_sound (w := (428525006219 / 2428525006219)) (n := 12)
    (lo := (356642447 / 1000000000)) (hi := (22290153 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1428525006219 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1428525006219 / 1000000000000) = 1/(500000000000 / 1428525006219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1049789627 / 1000000000) (1049789629 / 1000000000) (Real.log (1428525006219 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1428525006219 / 500000000000) = -Real.log (500000000000 / 1428525006219) := by
    rw [show ((1428525006219 / 500000000000) : ℝ) = ((500000000000 / 1428525006219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (527358073 / 500000000) ≤ -Real.log (500000000000 / 1435580025589) ∧
    -Real.log (500000000000 / 1435580025589) ≤ (263679037 / 250000000) := by
  have h := checkLog_sound (w := (435580025589 / 2435580025589)) (n := 12)
    (lo := (180784483 / 500000000)) (hi := (361568967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1435580025589 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1435580025589 / 1000000000000) = 1/(500000000000 / 1435580025589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (527358073 / 500000000) (263679037 / 250000000) (Real.log (1435580025589 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1435580025589 / 500000000000) = -Real.log (500000000000 / 1435580025589) := by
    rw [show ((1435580025589 / 500000000000) : ℝ) = ((500000000000 / 1435580025589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0083
