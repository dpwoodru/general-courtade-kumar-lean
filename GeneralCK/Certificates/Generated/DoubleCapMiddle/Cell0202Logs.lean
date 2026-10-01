import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0202
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

theorem reflection_log_1_neg : (132382613 / 500000000) ≤ -Real.log (320 / 417) ∧
    -Real.log (320 / 417) ≤ (264765227 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 737)) (n := 12)
    (lo := (132382613 / 500000000)) (hi := (264765227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((417 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(417 / 320) = 1/(320 / 417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (132382613 / 500000000) (264765227 / 1000000000) (Real.log (417 / 320)) := by
  have h := reflection_log_1_neg
  have he : Real.log (417 / 320) = -Real.log (320 / 417) := by
    rw [show ((417 / 320) : ℝ) = ((320 / 417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (45143653 / 125000000) ≤ -Real.log (223 / 320) ∧
    -Real.log (223 / 320) ≤ (14445969 / 40000000) := by
  have h := checkLog_sound (w := (97 / 543)) (n := 12)
    (lo := (45143653 / 125000000)) (hi := (14445969 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 223) = 1/(223 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-14445969 / 40000000) (-45143653 / 125000000) (Real.log (223 / 320)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (66078871 / 250000000) ≤ -Real.log (5120 / 6669) ∧
    -Real.log (5120 / 6669) ≤ (52863097 / 200000000) := by
  have h := checkLog_sound (w := (1549 / 11789)) (n := 12)
    (lo := (66078871 / 250000000)) (hi := (52863097 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6669 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6669 / 5120) = 1/(5120 / 6669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (66078871 / 250000000) (52863097 / 200000000) (Real.log (6669 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6669 / 5120) = -Real.log (5120 / 6669) := by
    rw [show ((6669 / 5120) : ℝ) = ((5120 / 6669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (36030877 / 100000000) ≤ -Real.log (3571 / 5120) ∧
    -Real.log (3571 / 5120) ≤ (360308771 / 1000000000) := by
  have h := checkLog_sound (w := (1549 / 8691)) (n := 12)
    (lo := (36030877 / 100000000)) (hi := (360308771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3571) = 1/(3571 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-360308771 / 1000000000) (-36030877 / 100000000) (Real.log (3571 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (473902269 / 1000000000) ≤ -Real.log (160 / 257) ∧
    -Real.log (160 / 257) ≤ (47390227 / 100000000) := by
  have h := checkLog_sound (w := (97 / 417)) (n := 12)
    (lo := (473902269 / 1000000000)) (hi := (47390227 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((257 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(257 / 160) = 1/(160 / 257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (473902269 / 1000000000) (47390227 / 100000000) (Real.log (257 / 160)) := by
  have h := reflection_log_5_neg
  have he : Real.log (257 / 160) = -Real.log (160 / 257) := by
    rw [show ((257 / 160) : ℝ) = ((160 / 257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (58252443 / 62500000) ≤ -Real.log (63 / 160) ∧
    -Real.log (63 / 160) ≤ (93203909 / 100000000) := by
  have h := checkLog_sound (w := (17 / 143)) (n := 12)
    (lo := (59722977 / 250000000)) (hi := (238891909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 63) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(80 / 63) = 1/(63 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-93203909 / 100000000) (-58252443 / 62500000) (Real.log (63 / 160)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (473172431 / 1000000000) ≤ -Real.log (2560 / 4109) ∧
    -Real.log (2560 / 4109) ≤ (29573277 / 62500000) := by
  have h := checkLog_sound (w := (1549 / 6669)) (n := 12)
    (lo := (473172431 / 1000000000)) (hi := (29573277 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4109 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4109 / 2560) = 1/(2560 / 4109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (473172431 / 1000000000) (29573277 / 62500000) (Real.log (4109 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (4109 / 2560) = -Real.log (2560 / 4109) := by
    rw [show ((4109 / 2560) : ℝ) = ((2560 / 4109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (929067317 / 1000000000) ≤ -Real.log (1011 / 2560) ∧
    -Real.log (1011 / 2560) ≤ (929067319 / 1000000000) := by
  have h := checkLog_sound (w := (269 / 2291)) (n := 12)
    (lo := (235920137 / 1000000000)) (hi := (117960069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 1011) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1280 / 1011) = 1/(1011 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-929067319 / 1000000000) (-929067317 / 1000000000) (Real.log (1011 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (361603777 / 1000000000) ≤ -Real.log (100000 / 143563) ∧
    -Real.log (100000 / 143563) ≤ (180801889 / 500000000) := by
  have h := checkLog_sound (w := (43563 / 243563)) (n := 12)
    (lo := (361603777 / 1000000000)) (hi := (180801889 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143563 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143563 / 100000) = 1/(100000 / 143563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (361603777 / 1000000000) (180801889 / 500000000) (Real.log (143563 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (143563 / 100000) = -Real.log (100000 / 143563) := by
    rw [show ((143563 / 100000) : ℝ) = ((100000 / 143563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (286022607 / 500000000) ≤ -Real.log (56437 / 100000) ∧
    -Real.log (56437 / 100000) ≤ (114409043 / 200000000) := by
  have h := checkLog_sound (w := (43563 / 156437)) (n := 12)
    (lo := (286022607 / 500000000)) (hi := (114409043 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 56437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 56437) = 1/(56437 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-114409043 / 200000000) (-286022607 / 500000000) (Real.log (56437 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (45277157 / 125000000) ≤ -Real.log (1000000 / 1436511) ∧
    -Real.log (1000000 / 1436511) ≤ (362217257 / 1000000000) := by
  have h := checkLog_sound (w := (436511 / 2436511)) (n := 12)
    (lo := (45277157 / 125000000)) (hi := (362217257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1436511 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1436511 / 1000000) = 1/(1000000 / 1436511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (45277157 / 125000000) (362217257 / 1000000000) (Real.log (1436511 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1436511 / 1000000) = -Real.log (1000000 / 1436511) := by
    rw [show ((1436511 / 1000000) : ℝ) = ((1000000 / 1436511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (286803733 / 500000000) ≤ -Real.log (563489 / 1000000) ∧
    -Real.log (563489 / 1000000) ≤ (573607467 / 1000000000) := by
  have h := checkLog_sound (w := (436511 / 1563489)) (n := 12)
    (lo := (286803733 / 500000000)) (hi := (573607467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 563489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 563489) = 1/(563489 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-573607467 / 1000000000) (-286803733 / 500000000) (Real.log (563489 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (140736417 / 500000000) ≤ -Real.log (25000 / 33127) ∧
    -Real.log (25000 / 33127) ≤ (56294567 / 200000000) := by
  have h := checkLog_sound (w := (8127 / 58127)) (n := 12)
    (lo := (140736417 / 500000000)) (hi := (56294567 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33127 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33127 / 25000) = 1/(25000 / 33127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (140736417 / 500000000) (56294567 / 200000000) (Real.log (33127 / 25000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (33127 / 25000) = -Real.log (25000 / 33127) := by
    rw [show ((33127 / 25000) : ℝ) = ((25000 / 33127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (393161113 / 1000000000) ≤ -Real.log (16873 / 25000) ∧
    -Real.log (16873 / 25000) ≤ (196580557 / 500000000) := by
  have h := checkLog_sound (w := (8127 / 41873)) (n := 12)
    (lo := (393161113 / 1000000000)) (hi := (196580557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 16873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 16873) = 1/(16873 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-196580557 / 500000000) (-393161113 / 1000000000) (Real.log (16873 / 25000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (282023593 / 1000000000) ≤ -Real.log (100000 / 132581) ∧
    -Real.log (100000 / 132581) ≤ (141011797 / 500000000) := by
  have h := checkLog_sound (w := (32581 / 232581)) (n := 12)
    (lo := (282023593 / 1000000000)) (hi := (141011797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((132581 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(132581 / 100000) = 1/(100000 / 132581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (282023593 / 1000000000) (141011797 / 500000000) (Real.log (132581 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (132581 / 100000) = -Real.log (100000 / 132581) := by
    rw [show ((132581 / 100000) : ℝ) = ((100000 / 132581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (98560827 / 250000000) ≤ -Real.log (67419 / 100000) ∧
    -Real.log (67419 / 100000) ≤ (394243309 / 1000000000) := by
  have h := checkLog_sound (w := (32581 / 167419)) (n := 12)
    (lo := (98560827 / 250000000)) (hi := (394243309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 67419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 67419) = 1/(67419 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-394243309 / 1000000000) (-98560827 / 250000000) (Real.log (67419 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (93364899 / 100000000) ≤ -Real.log (62500000000 / 158985904637) ∧
    -Real.log (62500000000 / 158985904637) ≤ (29176531 / 31250000) := by
  have h := checkLog_sound (w := (33985904637 / 283985904637)) (n := 12)
    (lo := (24050181 / 100000000)) (hi := (240501811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158985904637 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(158985904637 / 125000000000) = 1/(62500000000 / 158985904637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (93364899 / 100000000) (29176531 / 31250000) (Real.log (158985904637 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (158985904637 / 62500000000) = -Real.log (62500000000 / 158985904637) := by
    rw [show ((158985904637 / 62500000000) : ℝ) = ((62500000000 / 158985904637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (467912361 / 500000000) ≤ -Real.log (500000000000 / 1274657535463) ∧
    -Real.log (500000000000 / 1274657535463) ≤ (233956181 / 250000000) := by
  have h := checkLog_sound (w := (274657535463 / 2274657535463)) (n := 12)
    (lo := (121338771 / 500000000)) (hi := (242677543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1274657535463 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1274657535463 / 1000000000000) = 1/(500000000000 / 1274657535463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (467912361 / 500000000) (233956181 / 250000000) (Real.log (1274657535463 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1274657535463 / 500000000000) = -Real.log (500000000000 / 1274657535463) := by
    rw [show ((1274657535463 / 500000000000) : ℝ) = ((500000000000 / 1274657535463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (168658487 / 250000000) ≤ -Real.log (125000000000 / 245414271321) ∧
    -Real.log (125000000000 / 245414271321) ≤ (674633949 / 1000000000) := by
  have h := checkLog_sound (w := (120414271321 / 370414271321)) (n := 12)
    (lo := (168658487 / 250000000)) (hi := (674633949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((245414271321 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(245414271321 / 125000000000) = 1/(125000000000 / 245414271321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (168658487 / 250000000) (674633949 / 1000000000) (Real.log (245414271321 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (245414271321 / 125000000000) = -Real.log (125000000000 / 245414271321) := by
    rw [show ((245414271321 / 125000000000) : ℝ) = ((125000000000 / 245414271321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (338133451 / 500000000) ≤ -Real.log (125000000000 / 245815348789) ∧
    -Real.log (125000000000 / 245815348789) ≤ (676266903 / 1000000000) := by
  have h := checkLog_sound (w := (120815348789 / 370815348789)) (n := 12)
    (lo := (338133451 / 500000000)) (hi := (676266903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((245815348789 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(245815348789 / 125000000000) = 1/(125000000000 / 245815348789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (338133451 / 500000000) (676266903 / 1000000000) (Real.log (245815348789 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (245815348789 / 125000000000) = -Real.log (125000000000 / 245815348789) := by
    rw [show ((245815348789 / 125000000000) : ℝ) = ((125000000000 / 245815348789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0202
