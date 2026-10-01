import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0377
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

theorem reflection_log_1_neg : (205727137 / 1000000000) ≤ -Real.log (10240 / 12579) ∧
    -Real.log (10240 / 12579) ≤ (102863569 / 500000000) := by
  have h := checkLog_sound (w := (2339 / 22819)) (n := 12)
    (lo := (205727137 / 1000000000)) (hi := (102863569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12579 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12579 / 10240) = 1/(10240 / 12579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (205727137 / 1000000000) (102863569 / 500000000) (Real.log (12579 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12579 / 10240) = -Real.log (10240 / 12579) := by
    rw [show ((12579 / 10240) : ℝ) = ((10240 / 12579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (51862457 / 200000000) ≤ -Real.log (7901 / 10240) ∧
    -Real.log (7901 / 10240) ≤ (129656143 / 500000000) := by
  have h := checkLog_sound (w := (2339 / 18141)) (n := 12)
    (lo := (51862457 / 200000000)) (hi := (129656143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7901) = 1/(7901 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-129656143 / 500000000) (-51862457 / 200000000) (Real.log (7901 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (25686077 / 125000000) ≤ -Real.log (320 / 393) ∧
    -Real.log (320 / 393) ≤ (205488617 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 713)) (n := 12)
    (lo := (25686077 / 125000000)) (hi := (205488617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((393 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(393 / 320) = 1/(320 / 393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (25686077 / 125000000) (205488617 / 1000000000) (Real.log (393 / 320)) := by
  have h := reflection_log_3_neg
  have he : Real.log (393 / 320) = -Real.log (320 / 393) := by
    rw [show ((393 / 320) : ℝ) = ((320 / 393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (258932659 / 1000000000) ≤ -Real.log (247 / 320) ∧
    -Real.log (247 / 320) ≤ (12946633 / 50000000) := by
  have h := checkLog_sound (w := (73 / 567)) (n := 12)
    (lo := (258932659 / 1000000000)) (hi := (12946633 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 247) = 1/(247 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-12946633 / 50000000) (-258932659 / 1000000000) (Real.log (247 / 320)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (376266917 / 1000000000) ≤ -Real.log (5120 / 7459) ∧
    -Real.log (5120 / 7459) ≤ (188133459 / 500000000) := by
  have h := checkLog_sound (w := (2339 / 12579)) (n := 12)
    (lo := (376266917 / 1000000000)) (hi := (188133459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7459 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7459 / 5120) = 1/(5120 / 7459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (376266917 / 1000000000) (188133459 / 500000000) (Real.log (7459 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7459 / 5120) = -Real.log (5120 / 7459) := by
    rw [show ((7459 / 5120) : ℝ) = ((5120 / 7459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (610343863 / 1000000000) ≤ -Real.log (2781 / 5120) ∧
    -Real.log (2781 / 5120) ≤ (76292983 / 125000000) := by
  have h := checkLog_sound (w := (2339 / 7901)) (n := 12)
    (lo := (610343863 / 1000000000)) (hi := (76292983 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2781) = 1/(2781 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-76292983 / 125000000) (-610343863 / 1000000000) (Real.log (2781 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (187932319 / 500000000) ≤ -Real.log (160 / 233) ∧
    -Real.log (160 / 233) ≤ (375864639 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 393)) (n := 12)
    (lo := (187932319 / 500000000)) (hi := (375864639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233 / 160) = 1/(160 / 233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (187932319 / 500000000) (375864639 / 1000000000) (Real.log (233 / 160)) := by
  have h := reflection_log_7_neg
  have he : Real.log (233 / 160) = -Real.log (160 / 233) := by
    rw [show ((233 / 160) : ℝ) = ((160 / 233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (19039553 / 31250000) ≤ -Real.log (87 / 160) ∧
    -Real.log (87 / 160) ≤ (609265697 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 247)) (n := 12)
    (lo := (19039553 / 31250000)) (hi := (609265697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 87) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 87) = 1/(87 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-609265697 / 1000000000) (-19039553 / 31250000) (Real.log (87 / 160)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (281931569 / 1000000000) ≤ -Real.log (125000 / 165711) ∧
    -Real.log (125000 / 165711) ≤ (28193157 / 100000000) := by
  have h := checkLog_sound (w := (40711 / 290711)) (n := 12)
    (lo := (281931569 / 1000000000)) (hi := (28193157 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((165711 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(165711 / 125000) = 1/(125000 / 165711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (281931569 / 1000000000) (28193157 / 100000000) (Real.log (165711 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (165711 / 125000) = -Real.log (125000 / 165711) := by
    rw [show ((165711 / 125000) : ℝ) = ((125000 / 165711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (394062367 / 1000000000) ≤ -Real.log (84289 / 125000) ∧
    -Real.log (84289 / 125000) ≤ (12314449 / 31250000) := by
  have h := checkLog_sound (w := (40711 / 209289)) (n := 12)
    (lo := (394062367 / 1000000000)) (hi := (12314449 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 84289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 84289) = 1/(84289 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-12314449 / 31250000) (-394062367 / 1000000000) (Real.log (84289 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (282254369 / 1000000000) ≤ -Real.log (250000 / 331529) ∧
    -Real.log (250000 / 331529) ≤ (28225437 / 100000000) := by
  have h := checkLog_sound (w := (81529 / 581529)) (n := 12)
    (lo := (282254369 / 1000000000)) (hi := (28225437 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((331529 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(331529 / 250000) = 1/(250000 / 331529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (282254369 / 1000000000) (28225437 / 100000000) (Real.log (331529 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (331529 / 250000) = -Real.log (250000 / 331529) := by
    rw [show ((331529 / 250000) : ℝ) = ((250000 / 331529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (394697289 / 1000000000) ≤ -Real.log (168471 / 250000) ∧
    -Real.log (168471 / 250000) ≤ (39469729 / 100000000) := by
  have h := checkLog_sound (w := (81529 / 418471)) (n := 12)
    (lo := (394697289 / 1000000000)) (hi := (39469729 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 168471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 168471) = 1/(168471 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-39469729 / 100000000) (-394697289 / 1000000000) (Real.log (168471 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (212900873 / 1000000000) ≤ -Real.log (500000 / 618631) ∧
    -Real.log (500000 / 618631) ≤ (106450437 / 500000000) := by
  have h := checkLog_sound (w := (118631 / 1118631)) (n := 12)
    (lo := (212900873 / 1000000000)) (hi := (106450437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((618631 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(618631 / 500000) = 1/(500000 / 618631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (212900873 / 1000000000) (106450437 / 500000000) (Real.log (618631 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (618631 / 500000) = -Real.log (500000 / 618631) := by
    rw [show ((618631 / 500000) : ℝ) = ((500000 / 618631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (16927543 / 62500000) ≤ -Real.log (381369 / 500000) ∧
    -Real.log (381369 / 500000) ≤ (270840689 / 1000000000) := by
  have h := checkLog_sound (w := (118631 / 881369)) (n := 12)
    (lo := (16927543 / 62500000)) (hi := (270840689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 381369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 381369) = 1/(381369 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-270840689 / 1000000000) (-16927543 / 62500000) (Real.log (381369 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (53292091 / 250000000) ≤ -Real.log (1000000 / 1237593) ∧
    -Real.log (1000000 / 1237593) ≤ (42633673 / 200000000) := by
  have h := checkLog_sound (w := (237593 / 2237593)) (n := 12)
    (lo := (53292091 / 250000000)) (hi := (42633673 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1237593 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1237593 / 1000000) = 1/(1000000 / 1237593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (53292091 / 250000000) (42633673 / 200000000) (Real.log (1237593 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1237593 / 1000000) = -Real.log (1000000 / 1237593) := by
    rw [show ((1237593 / 1000000) : ℝ) = ((1000000 / 1237593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (54254949 / 200000000) ≤ -Real.log (762407 / 1000000) ∧
    -Real.log (762407 / 1000000) ≤ (135637373 / 500000000) := by
  have h := checkLog_sound (w := (237593 / 1762407)) (n := 12)
    (lo := (54254949 / 200000000)) (hi := (135637373 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 762407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 762407) = 1/(762407 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-135637373 / 500000000) (-54254949 / 200000000) (Real.log (762407 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (675993937 / 1000000000) ≤ -Real.log (62500000000 / 122874129483) ∧
    -Real.log (62500000000 / 122874129483) ≤ (337996969 / 500000000) := by
  have h := checkLog_sound (w := (60374129483 / 185374129483)) (n := 12)
    (lo := (675993937 / 1000000000)) (hi := (337996969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122874129483 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122874129483 / 62500000000) = 1/(62500000000 / 122874129483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (675993937 / 1000000000) (337996969 / 500000000) (Real.log (122874129483 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (122874129483 / 62500000000) = -Real.log (62500000000 / 122874129483) := by
    rw [show ((122874129483 / 62500000000) : ℝ) = ((62500000000 / 122874129483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (338475829 / 500000000) ≤ -Real.log (500000000000 / 983934920551) ∧
    -Real.log (500000000000 / 983934920551) ≤ (676951659 / 1000000000) := by
  have h := checkLog_sound (w := (483934920551 / 1483934920551)) (n := 12)
    (lo := (338475829 / 500000000)) (hi := (676951659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983934920551 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983934920551 / 500000000000) = 1/(500000000000 / 983934920551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (338475829 / 500000000) (676951659 / 1000000000) (Real.log (983934920551 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (983934920551 / 500000000000) = -Real.log (500000000000 / 983934920551) := by
    rw [show ((983934920551 / 500000000000) : ℝ) = ((500000000000 / 983934920551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (483741561 / 1000000000) ≤ -Real.log (500000000000 / 811066185243) ∧
    -Real.log (500000000000 / 811066185243) ≤ (241870781 / 500000000) := by
  have h := checkLog_sound (w := (311066185243 / 1311066185243)) (n := 12)
    (lo := (483741561 / 1000000000)) (hi := (241870781 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((811066185243 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(811066185243 / 500000000000) = 1/(500000000000 / 811066185243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (483741561 / 1000000000) (241870781 / 500000000) (Real.log (811066185243 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (811066185243 / 500000000000) = -Real.log (500000000000 / 811066185243) := by
    rw [show ((811066185243 / 500000000000) : ℝ) = ((500000000000 / 811066185243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (484443109 / 1000000000) ≤ -Real.log (500000000000 / 811635386349) ∧
    -Real.log (500000000000 / 811635386349) ≤ (48444311 / 100000000) := by
  have h := checkLog_sound (w := (311635386349 / 1311635386349)) (n := 12)
    (lo := (484443109 / 1000000000)) (hi := (48444311 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((811635386349 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(811635386349 / 500000000000) = 1/(500000000000 / 811635386349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (484443109 / 1000000000) (48444311 / 100000000) (Real.log (811635386349 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (811635386349 / 500000000000) = -Real.log (500000000000 / 811635386349) := by
    rw [show ((811635386349 / 500000000000) : ℝ) = ((500000000000 / 811635386349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0377
