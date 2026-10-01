import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0038
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

theorem reflection_log_1_neg : (192072853 / 500000000) ≤ -Real.log (2560 / 3759) ∧
    -Real.log (2560 / 3759) ≤ (384145707 / 1000000000) := by
  have h := checkLog_sound (w := (1199 / 6319)) (n := 12)
    (lo := (192072853 / 500000000)) (hi := (384145707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3759 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3759 / 2560) = 1/(2560 / 3759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (192072853 / 500000000) (384145707 / 1000000000) (Real.log (3759 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3759 / 2560) = -Real.log (2560 / 3759) := by
    rw [show ((3759 / 2560) : ℝ) = ((2560 / 3759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (315893767 / 500000000) ≤ -Real.log (1361 / 2560) ∧
    -Real.log (1361 / 2560) ≤ (126357507 / 200000000) := by
  have h := checkLog_sound (w := (1199 / 3921)) (n := 12)
    (lo := (315893767 / 500000000)) (hi := (126357507 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1361) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1361) = 1/(1361 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-126357507 / 200000000) (-315893767 / 500000000) (Real.log (1361 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (191673651 / 500000000) ≤ -Real.log (640 / 939) ∧
    -Real.log (640 / 939) ≤ (383347303 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 1579)) (n := 12)
    (lo := (191673651 / 500000000)) (hi := (383347303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((939 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(939 / 640) = 1/(640 / 939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (191673651 / 500000000) (383347303 / 1000000000) (Real.log (939 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (939 / 640) = -Real.log (640 / 939) := by
    rw [show ((939 / 640) : ℝ) = ((640 / 939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (629585699 / 1000000000) ≤ -Real.log (341 / 640) ∧
    -Real.log (341 / 640) ≤ (6295857 / 10000000) := by
  have h := checkLog_sound (w := (299 / 981)) (n := 12)
    (lo := (629585699 / 1000000000)) (hi := (6295857 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 341) = 1/(341 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6295857 / 10000000) (-629585699 / 1000000000) (Real.log (341 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (26439807 / 40000000) ≤ -Real.log (1280 / 2479) ∧
    -Real.log (1280 / 2479) ≤ (82624397 / 125000000) := by
  have h := checkLog_sound (w := (1199 / 3759)) (n := 12)
    (lo := (26439807 / 40000000)) (hi := (82624397 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2479 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2479 / 1280) = 1/(1280 / 2479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (26439807 / 40000000) (82624397 / 125000000) (Real.log (2479 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2479 / 1280) = -Real.log (1280 / 2479) := by
    rw [show ((2479 / 1280) : ℝ) = ((1280 / 2479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (13800831 / 5000000) ≤ -Real.log (81 / 1280) ∧
    -Real.log (81 / 1280) ≤ (690041551 / 250000000) := by
  have h := checkLog_sound (w := (79 / 241)) (n := 12)
    (lo := (34036233 / 50000000)) (hi := (680724661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 81) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 81) = 1/(81 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-690041551 / 250000000) (-13800831 / 5000000) (Real.log (81 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (164946069 / 250000000) ≤ -Real.log (320 / 619) ∧
    -Real.log (320 / 619) ≤ (659784277 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 939)) (n := 12)
    (lo := (164946069 / 250000000)) (hi := (659784277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((619 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(619 / 320) = 1/(320 / 619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (164946069 / 250000000) (659784277 / 1000000000) (Real.log (619 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (619 / 320) = -Real.log (320 / 619) := by
    rw [show ((619 / 320) : ℝ) = ((320 / 619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (680949639 / 250000000) ≤ -Real.log (21 / 320) ∧
    -Real.log (21 / 320) ≤ (17023741 / 6250000) := by
  have h := checkLog_sound (w := (19 / 61)) (n := 12)
    (lo := (80544627 / 125000000)) (hi := (644357017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 21) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(40 / 21) = 1/(21 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-17023741 / 6250000) (-680949639 / 250000000) (Real.log (21 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (533284719 / 1000000000) ≤ -Real.log (500000 / 852261) ∧
    -Real.log (500000 / 852261) ≤ (6666059 / 12500000) := by
  have h := checkLog_sound (w := (352261 / 1352261)) (n := 12)
    (lo := (533284719 / 1000000000)) (hi := (6666059 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((852261 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(852261 / 500000) = 1/(500000 / 852261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (533284719 / 1000000000) (6666059 / 12500000) (Real.log (852261 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (852261 / 500000) = -Real.log (500000 / 852261) := by
    rw [show ((852261 / 500000) : ℝ) = ((500000 / 852261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (609580447 / 500000000) ≤ -Real.log (147739 / 500000) ∧
    -Real.log (147739 / 500000) ≤ (19049389 / 15625000) := by
  have h := checkLog_sound (w := (102261 / 397739)) (n := 12)
    (lo := (263006857 / 500000000)) (hi := (105202743 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 147739) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 147739) = 1/(147739 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-19049389 / 15625000) (-609580447 / 500000000) (Real.log (147739 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (106923117 / 200000000) ≤ -Real.log (125000 / 213349) ∧
    -Real.log (125000 / 213349) ≤ (267307793 / 500000000) := by
  have h := checkLog_sound (w := (88349 / 338349)) (n := 12)
    (lo := (106923117 / 200000000)) (hi := (267307793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((213349 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(213349 / 125000) = 1/(125000 / 213349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (106923117 / 200000000) (267307793 / 500000000) (Real.log (213349 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (213349 / 125000) = -Real.log (125000 / 213349) := by
    rw [show ((213349 / 125000) : ℝ) = ((125000 / 213349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1226873023 / 1000000000) ≤ -Real.log (36651 / 125000) ∧
    -Real.log (36651 / 125000) ≤ (49074921 / 40000000) := by
  have h := checkLog_sound (w := (25849 / 99151)) (n := 12)
    (lo := (533725843 / 1000000000)) (hi := (133431461 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 36651) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 36651) = 1/(36651 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-49074921 / 40000000) (-1226873023 / 1000000000) (Real.log (36651 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (455009273 / 1000000000) ≤ -Real.log (250000 / 394047) ∧
    -Real.log (250000 / 394047) ≤ (227504637 / 500000000) := by
  have h := checkLog_sound (w := (144047 / 644047)) (n := 12)
    (lo := (455009273 / 1000000000)) (hi := (227504637 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394047 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394047 / 250000) = 1/(250000 / 394047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (455009273 / 1000000000) (227504637 / 500000000) (Real.log (394047 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (394047 / 250000) = -Real.log (250000 / 394047) := by
    rw [show ((394047 / 250000) : ℝ) = ((250000 / 394047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (858465317 / 1000000000) ≤ -Real.log (105953 / 250000) ∧
    -Real.log (105953 / 250000) ≤ (858465319 / 1000000000) := by
  have h := checkLog_sound (w := (19047 / 230953)) (n := 12)
    (lo := (165318137 / 1000000000)) (hi := (82659069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 105953) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 105953) = 1/(105953 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-858465319 / 1000000000) (-858465317 / 1000000000) (Real.log (105953 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (114135703 / 250000000) ≤ -Real.log (1000000 / 1578607) ∧
    -Real.log (1000000 / 1578607) ≤ (456542813 / 1000000000) := by
  have h := checkLog_sound (w := (578607 / 2578607)) (n := 12)
    (lo := (114135703 / 250000000)) (hi := (456542813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1578607 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1578607 / 1000000) = 1/(1000000 / 1578607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (114135703 / 250000000) (456542813 / 1000000000) (Real.log (1578607 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1578607 / 1000000) = -Real.log (1000000 / 1578607) := by
    rw [show ((1578607 / 1000000) : ℝ) = ((1000000 / 1578607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (216047347 / 250000000) ≤ -Real.log (421393 / 1000000) ∧
    -Real.log (421393 / 1000000) ≤ (86418939 / 100000000) := by
  have h := checkLog_sound (w := (78607 / 921393)) (n := 12)
    (lo := (5345069 / 31250000)) (hi := (171042209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 421393) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 421393) = 1/(421393 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-86418939 / 100000000) (-216047347 / 250000000) (Real.log (421393 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1752445613 / 1000000000) ≤ -Real.log (7812500000 / 45067917493) ∧
    -Real.log (7812500000 / 45067917493) ≤ (109527851 / 62500000) := by
  have h := checkLog_sound (w := (13817917493 / 76317917493)) (n := 12)
    (lo := (366151253 / 1000000000)) (hi := (183075627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45067917493 / 31250000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(45067917493 / 31250000000) = 1/(7812500000 / 45067917493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1752445613 / 1000000000) (109527851 / 62500000) (Real.log (45067917493 / 7812500000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (45067917493 / 7812500000) = -Real.log (7812500000 / 45067917493) := by
    rw [show ((45067917493 / 7812500000) : ℝ) = ((7812500000 / 45067917493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (55046519 / 31250000) ≤ -Real.log (250000000000 / 1455274071649) ∧
    -Real.log (250000000000 / 1455274071649) ≤ (1761488611 / 1000000000) := by
  have h := checkLog_sound (w := (455274071649 / 2455274071649)) (n := 12)
    (lo := (46899281 / 125000000)) (hi := (375194249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1455274071649 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1455274071649 / 1000000000000) = 1/(250000000000 / 1455274071649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (55046519 / 31250000) (1761488611 / 1000000000) (Real.log (1455274071649 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1455274071649 / 250000000000) = -Real.log (250000000000 / 1455274071649) := by
    rw [show ((1455274071649 / 250000000000) : ℝ) = ((250000000000 / 1455274071649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1313474591 / 1000000000) ≤ -Real.log (25000000000 / 92976838787) ∧
    -Real.log (25000000000 / 92976838787) ≤ (1313474593 / 1000000000) := by
  have h := checkLog_sound (w := (42976838787 / 142976838787)) (n := 12)
    (lo := (620327411 / 1000000000)) (hi := (155081853 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92976838787 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(92976838787 / 50000000000) = 1/(25000000000 / 92976838787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1313474591 / 1000000000) (1313474593 / 1000000000) (Real.log (92976838787 / 25000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (92976838787 / 25000000000) = -Real.log (25000000000 / 92976838787) := by
    rw [show ((92976838787 / 25000000000) : ℝ) = ((25000000000 / 92976838787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1320732201 / 1000000000) ≤ -Real.log (250000000000 / 936540830057) ∧
    -Real.log (250000000000 / 936540830057) ≤ (1320732203 / 1000000000) := by
  have h := checkLog_sound (w := (436540830057 / 1436540830057)) (n := 12)
    (lo := (627585021 / 1000000000)) (hi := (313792511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((936540830057 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(936540830057 / 500000000000) = 1/(250000000000 / 936540830057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1320732201 / 1000000000) (1320732203 / 1000000000) (Real.log (936540830057 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (936540830057 / 250000000000) = -Real.log (250000000000 / 936540830057) := by
    rw [show ((936540830057 / 250000000000) : ℝ) = ((250000000000 / 936540830057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0038
