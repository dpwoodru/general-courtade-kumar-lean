import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0084
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

theorem reflection_log_1_neg : (86685743 / 250000000) ≤ -Real.log (2560 / 3621) ∧
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


theorem reflection_log_1 : Bounds (86685743 / 250000000) (346742973 / 1000000000) (Real.log (3621 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3621 / 2560) = -Real.log (2560 / 3621) := by
    rw [show ((3621 / 2560) : ℝ) = ((2560 / 3621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (535209039 / 1000000000) ≤ -Real.log (1499 / 2560) ∧
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


theorem reflection_log_2 : Bounds (-6690113 / 12500000) (-535209039 / 1000000000) (Real.log (1499 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (21619633 / 62500000) ≤ -Real.log (1280 / 1809) ∧
    -Real.log (1280 / 1809) ≤ (345914129 / 1000000000) := by
  have h := checkLog_sound (w := (529 / 3089)) (n := 12)
    (lo := (21619633 / 62500000)) (hi := (345914129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1809 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1809 / 1280) = 1/(1280 / 1809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (21619633 / 62500000) (345914129 / 1000000000) (Real.log (1809 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1809 / 1280) = -Real.log (1280 / 1809) := by
    rw [show ((1809 / 1280) : ℝ) = ((1280 / 1809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (106641941 / 200000000) ≤ -Real.log (751 / 1280) ∧
    -Real.log (751 / 1280) ≤ (266604853 / 500000000) := by
  have h := checkLog_sound (w := (529 / 2031)) (n := 12)
    (lo := (106641941 / 200000000)) (hi := (266604853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 751) = 1/(751 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-266604853 / 500000000) (-106641941 / 200000000) (Real.log (751 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (60371811 / 100000000) ≤ -Real.log (1280 / 2341) ∧
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


theorem reflection_log_5 : Bounds (60371811 / 100000000) (603718111 / 1000000000) (Real.log (2341 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2341 / 1280) = -Real.log (1280 / 2341) := by
    rw [show ((2341 / 1280) : ℝ) = ((1280 / 2341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (14124349 / 8000000) ≤ -Real.log (219 / 1280) ∧
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


theorem reflection_log_6 : Bounds (-441385907 / 250000000) (-14124349 / 8000000) (Real.log (219 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (120487157 / 200000000) ≤ -Real.log (640 / 1169) ∧
    -Real.log (640 / 1169) ≤ (301217893 / 500000000) := by
  have h := checkLog_sound (w := (529 / 1809)) (n := 12)
    (lo := (120487157 / 200000000)) (hi := (301217893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1169 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1169 / 640) = 1/(640 / 1169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (120487157 / 200000000) (301217893 / 500000000) (Real.log (1169 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1169 / 640) = -Real.log (640 / 1169) := by
    rw [show ((1169 / 640) : ℝ) = ((640 / 1169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1751937973 / 1000000000) ≤ -Real.log (111 / 640) ∧
    -Real.log (111 / 640) ≤ (218992247 / 125000000) := by
  have h := checkLog_sound (w := (49 / 271)) (n := 12)
    (lo := (365643613 / 1000000000)) (hi := (182821807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 111) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 111) = 1/(111 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-218992247 / 125000000) (-1751937973 / 1000000000) (Real.log (111 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (29730543 / 62500000) ≤ -Real.log (500000 / 804561) ∧
    -Real.log (500000 / 804561) ≤ (475688689 / 1000000000) := by
  have h := checkLog_sound (w := (304561 / 1304561)) (n := 12)
    (lo := (29730543 / 62500000)) (hi := (475688689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((804561 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(804561 / 500000) = 1/(500000 / 804561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (29730543 / 62500000) (475688689 / 1000000000) (Real.log (804561 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (804561 / 500000) = -Real.log (500000 / 804561) := by
    rw [show ((804561 / 500000) : ℝ) = ((500000 / 804561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (939359787 / 1000000000) ≤ -Real.log (195439 / 500000) ∧
    -Real.log (195439 / 500000) ≤ (939359789 / 1000000000) := by
  have h := checkLog_sound (w := (54561 / 445439)) (n := 12)
    (lo := (246212607 / 1000000000)) (hi := (480884 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 195439) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 195439) = 1/(195439 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-939359789 / 1000000000) (-939359787 / 1000000000) (Real.log (195439 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (238450829 / 500000000) ≤ -Real.log (40000 / 64443) ∧
    -Real.log (40000 / 64443) ≤ (476901659 / 1000000000) := by
  have h := checkLog_sound (w := (24443 / 104443)) (n := 12)
    (lo := (238450829 / 500000000)) (hi := (476901659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64443 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64443 / 40000) = 1/(40000 / 64443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (238450829 / 500000000) (476901659 / 1000000000) (Real.log (64443 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (64443 / 40000) = -Real.log (40000 / 64443) := by
    rw [show ((64443 / 40000) : ℝ) = ((40000 / 64443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (188873751 / 200000000) ≤ -Real.log (15557 / 40000) ∧
    -Real.log (15557 / 40000) ≤ (944368757 / 1000000000) := by
  have h := checkLog_sound (w := (4443 / 35557)) (n := 12)
    (lo := (10048863 / 40000000)) (hi := (31402697 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 15557) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 15557) = 1/(15557 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-944368757 / 1000000000) (-188873751 / 200000000) (Real.log (15557 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (195881497 / 500000000) ≤ -Real.log (1000000 / 1479587) ∧
    -Real.log (1000000 / 1479587) ≤ (78352599 / 200000000) := by
  have h := checkLog_sound (w := (479587 / 2479587)) (n := 12)
    (lo := (195881497 / 500000000)) (hi := (78352599 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1479587 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1479587 / 1000000) = 1/(1000000 / 1479587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (195881497 / 500000000) (78352599 / 200000000) (Real.log (1479587 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1479587 / 1000000) = -Real.log (1000000 / 1479587) := by
    rw [show ((1479587 / 1000000) : ℝ) = ((1000000 / 1479587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (653132551 / 1000000000) ≤ -Real.log (520413 / 1000000) ∧
    -Real.log (520413 / 1000000) ≤ (81641569 / 125000000) := by
  have h := checkLog_sound (w := (479587 / 1520413)) (n := 12)
    (lo := (653132551 / 1000000000)) (hi := (81641569 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 520413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 520413) = 1/(520413 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-81641569 / 125000000) (-653132551 / 1000000000) (Real.log (520413 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (196517419 / 500000000) ≤ -Real.log (100000 / 148147) ∧
    -Real.log (100000 / 148147) ≤ (393034839 / 1000000000) := by
  have h := checkLog_sound (w := (48147 / 248147)) (n := 12)
    (lo := (196517419 / 500000000)) (hi := (393034839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148147 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148147 / 100000) = 1/(100000 / 148147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (196517419 / 500000000) (393034839 / 1000000000) (Real.log (148147 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (148147 / 100000) = -Real.log (100000 / 148147) := by
    rw [show ((148147 / 100000) : ℝ) = ((100000 / 148147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (656757393 / 1000000000) ≤ -Real.log (51853 / 100000) ∧
    -Real.log (51853 / 100000) ≤ (328378697 / 500000000) := by
  have h := checkLog_sound (w := (48147 / 151853)) (n := 12)
    (lo := (656757393 / 1000000000)) (hi := (328378697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 51853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 51853) = 1/(51853 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-328378697 / 500000000) (-656757393 / 1000000000) (Real.log (51853 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (56601939 / 40000000) ≤ -Real.log (500000000000 / 2058343012397) ∧
    -Real.log (500000000000 / 2058343012397) ≤ (707524239 / 500000000) := by
  have h := checkLog_sound (w := (58343012397 / 4058343012397)) (n := 12)
    (lo := (5750823 / 200000000)) (hi := (7188529 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2058343012397 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2058343012397 / 2000000000000) = 1/(500000000000 / 2058343012397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (56601939 / 40000000) (707524239 / 500000000) (Real.log (2058343012397 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2058343012397 / 500000000000) = -Real.log (500000000000 / 2058343012397) := by
    rw [show ((2058343012397 / 500000000000) : ℝ) = ((500000000000 / 2058343012397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (355317603 / 250000000) ≤ -Real.log (500000000000 / 2071189818089) ∧
    -Real.log (500000000000 / 2071189818089) ≤ (284254083 / 200000000) := by
  have h := checkLog_sound (w := (71189818089 / 4071189818089)) (n := 12)
    (lo := (8744013 / 250000000)) (hi := (34976053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2071189818089 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2071189818089 / 2000000000000) = 1/(500000000000 / 2071189818089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (355317603 / 250000000) (284254083 / 200000000) (Real.log (2071189818089 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2071189818089 / 500000000000) = -Real.log (500000000000 / 2071189818089) := by
    rw [show ((2071189818089 / 500000000000) : ℝ) = ((500000000000 / 2071189818089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (522447773 / 500000000) ≤ -Real.log (125000000000 / 355387692083) ∧
    -Real.log (125000000000 / 355387692083) ≤ (261223887 / 250000000) := by
  have h := checkLog_sound (w := (105387692083 / 605387692083)) (n := 12)
    (lo := (175874183 / 500000000)) (hi := (351748367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355387692083 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(355387692083 / 250000000000) = 1/(125000000000 / 355387692083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (522447773 / 500000000) (261223887 / 250000000) (Real.log (355387692083 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (355387692083 / 125000000000) = -Real.log (125000000000 / 355387692083) := by
    rw [show ((355387692083 / 125000000000) : ℝ) = ((125000000000 / 355387692083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1049792231 / 1000000000) ≤ -Real.log (125000000000 / 357132181359) ∧
    -Real.log (125000000000 / 357132181359) ≤ (1049792233 / 1000000000) := by
  have h := checkLog_sound (w := (107132181359 / 607132181359)) (n := 12)
    (lo := (356645051 / 1000000000)) (hi := (89161263 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357132181359 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(357132181359 / 250000000000) = 1/(125000000000 / 357132181359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1049792231 / 1000000000) (1049792233 / 1000000000) (Real.log (357132181359 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (357132181359 / 125000000000) = -Real.log (125000000000 / 357132181359) := by
    rw [show ((357132181359 / 125000000000) : ℝ) = ((125000000000 / 357132181359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0084
