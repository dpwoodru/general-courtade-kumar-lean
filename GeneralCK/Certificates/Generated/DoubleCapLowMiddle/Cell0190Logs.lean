import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0190
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

theorem reflection_log_1_neg : (305010147 / 500000000) ≤ -Real.log (6400 / 11779) ∧
    -Real.log (6400 / 11779) ≤ (122004059 / 200000000) := by
  have h := checkLog_sound (w := (5379 / 18179)) (n := 12)
    (lo := (305010147 / 500000000)) (hi := (122004059 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11779 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11779 / 6400) = 1/(6400 / 11779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (305010147 / 500000000) (122004059 / 200000000) (Real.log (11779 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (11779 / 6400) = -Real.log (6400 / 11779) := by
    rw [show ((11779 / 6400) : ℝ) = ((6400 / 11779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (36710309 / 20000000) ≤ -Real.log (1021 / 6400) ∧
    -Real.log (1021 / 6400) ≤ (1835515453 / 1000000000) := by
  have h := checkLog_sound (w := (579 / 2621)) (n := 12)
    (lo := (44922109 / 100000000)) (hi := (449221091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1021) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1021) = 1/(1021 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1835515453 / 1000000000) (-36710309 / 20000000) (Real.log (1021 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (9506343 / 15625000) ≤ -Real.log (80 / 147) ∧
    -Real.log (80 / 147) ≤ (608405953 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 227)) (n := 12)
    (lo := (9506343 / 15625000)) (hi := (608405953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147 / 80) = 1/(80 / 147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (9506343 / 15625000) (608405953 / 1000000000) (Real.log (147 / 80)) := by
  have h := reflection_log_3_neg
  have he : Real.log (147 / 80) = -Real.log (80 / 147) := by
    rw [show ((147 / 80) : ℝ) = ((80 / 147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (454269319 / 250000000) ≤ -Real.log (13 / 80) ∧
    -Real.log (13 / 80) ≤ (1817077279 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 33)) (n := 12)
    (lo := (107695729 / 250000000)) (hi := (430782917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 13) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(20 / 13) = 1/(13 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1817077279 / 1000000000) (-454269319 / 250000000) (Real.log (13 / 80)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (519351673 / 1000000000) ≤ -Real.log (3200 / 5379) ∧
    -Real.log (3200 / 5379) ≤ (259675837 / 500000000) := by
  have h := checkLog_sound (w := (2179 / 8579)) (n := 12)
    (lo := (519351673 / 1000000000)) (hi := (259675837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5379 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5379 / 3200) = 1/(3200 / 5379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (519351673 / 1000000000) (259675837 / 500000000) (Real.log (5379 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5379 / 3200) = -Real.log (3200 / 5379) := by
    rw [show ((5379 / 3200) : ℝ) = ((3200 / 5379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (114236827 / 100000000) ≤ -Real.log (1021 / 3200) ∧
    -Real.log (1021 / 3200) ≤ (71398017 / 62500000) := by
  have h := checkLog_sound (w := (579 / 2621)) (n := 12)
    (lo := (44922109 / 100000000)) (hi := (449221091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1021) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 1021) = 1/(1021 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-71398017 / 62500000) (-114236827 / 100000000) (Real.log (1021 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (103162633 / 200000000) ≤ -Real.log (40 / 67) ∧
    -Real.log (40 / 67) ≤ (257906583 / 500000000) := by
  have h := checkLog_sound (w := (27 / 107)) (n := 12)
    (lo := (103162633 / 200000000)) (hi := (257906583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67 / 40) = 1/(40 / 67) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (103162633 / 200000000) (257906583 / 500000000) (Real.log (67 / 40)) := by
  have h := reflection_log_7_neg
  have he : Real.log (67 / 40) = -Real.log (40 / 67) := by
    rw [show ((67 / 40) : ℝ) = ((40 / 67) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (70245631 / 62500000) ≤ -Real.log (13 / 40) ∧
    -Real.log (13 / 40) ≤ (561965049 / 500000000) := by
  have h := checkLog_sound (w := (7 / 33)) (n := 12)
    (lo := (107695729 / 250000000)) (hi := (430782917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 13) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20 / 13) = 1/(13 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-561965049 / 500000000) (-70245631 / 62500000) (Real.log (13 / 40)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (2473511 / 3906250) ≤ -Real.log (62500 / 117729) ∧
    -Real.log (62500 / 117729) ≤ (633218817 / 1000000000) := by
  have h := checkLog_sound (w := (55229 / 180229)) (n := 12)
    (lo := (2473511 / 3906250)) (hi := (633218817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117729 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117729 / 62500) = 1/(62500 / 117729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (2473511 / 3906250) (633218817 / 1000000000) (Real.log (117729 / 62500)) := by
  have h := reflection_log_9_neg
  have he : Real.log (117729 / 62500) = -Real.log (62500 / 117729) := by
    rw [show ((117729 / 62500) : ℝ) = ((62500 / 117729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2151272721 / 1000000000) ≤ -Real.log (7271 / 62500) ∧
    -Real.log (7271 / 62500) ≤ (86050909 / 40000000) := by
  have h := checkLog_sound (w := (1083 / 30167)) (n := 12)
    (lo := (71831181 / 1000000000)) (hi := (35915591 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 14542) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 14542) = 1/(7271 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-86050909 / 40000000) (-2151272721 / 1000000000) (Real.log (7271 / 62500)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (634150607 / 1000000000) ≤ -Real.log (50000 / 94271) ∧
    -Real.log (50000 / 94271) ≤ (39634413 / 62500000) := by
  have h := checkLog_sound (w := (44271 / 144271)) (n := 12)
    (lo := (634150607 / 1000000000)) (hi := (39634413 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((94271 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(94271 / 50000) = 1/(50000 / 94271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (634150607 / 1000000000) (39634413 / 62500000) (Real.log (94271 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (94271 / 50000) = -Real.log (50000 / 94271) := by
    rw [show ((94271 / 50000) : ℝ) = ((50000 / 94271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (270810251 / 125000000) ≤ -Real.log (5729 / 50000) ∧
    -Real.log (5729 / 50000) ≤ (541620503 / 250000000) := by
  have h := checkLog_sound (w := (521 / 11979)) (n := 12)
    (lo := (21760117 / 250000000)) (hi := (87040469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5729) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6250 / 5729) = 1/(5729 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-541620503 / 250000000) (-270810251 / 125000000) (Real.log (5729 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (314626359 / 500000000) ≤ -Real.log (62500 / 117263) ∧
    -Real.log (62500 / 117263) ≤ (629252719 / 1000000000) := by
  have h := checkLog_sound (w := (54763 / 179763)) (n := 12)
    (lo := (314626359 / 500000000)) (hi := (629252719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117263 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117263 / 62500) = 1/(62500 / 117263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (314626359 / 500000000) (629252719 / 1000000000) (Real.log (117263 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (117263 / 62500) = -Real.log (62500 / 117263) := by
    rw [show ((117263 / 62500) : ℝ) = ((62500 / 117263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2089152539 / 1000000000) ≤ -Real.log (7737 / 62500) ∧
    -Real.log (7737 / 62500) ≤ (2089152543 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 31099)) (n := 12)
    (lo := (9710999 / 1000000000)) (hi := (9711 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15474) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(15625 / 15474) = 1/(7737 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2089152543 / 1000000000) (-2089152539 / 1000000000) (Real.log (7737 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (315179829 / 500000000) ≤ -Real.log (500000 / 939143) ∧
    -Real.log (500000 / 939143) ≤ (630359659 / 1000000000) := by
  have h := checkLog_sound (w := (439143 / 1439143)) (n := 12)
    (lo := (315179829 / 500000000)) (hi := (630359659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((939143 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(939143 / 500000) = 1/(500000 / 939143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (315179829 / 500000000) (630359659 / 1000000000) (Real.log (939143 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (939143 / 500000) = -Real.log (500000 / 939143) := by
    rw [show ((939143 / 500000) : ℝ) = ((500000 / 939143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1053040623 / 500000000) ≤ -Real.log (60857 / 500000) ∧
    -Real.log (60857 / 500000) ≤ (336973 / 160000) := by
  have h := checkLog_sound (w := (1643 / 123357)) (n := 12)
    (lo := (13319853 / 500000000)) (hi := (26639707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 60857) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(62500 / 60857) = 1/(60857 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-336973 / 160000) (-1053040623 / 500000000) (Real.log (60857 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2784491537 / 1000000000) ≤ -Real.log (500000000000 / 8095791500481) ∧
    -Real.log (500000000000 / 8095791500481) ≤ (1392245771 / 500000000) := by
  have h := checkLog_sound (w := (95791500481 / 16095791500481)) (n := 12)
    (lo := (11902817 / 1000000000)) (hi := (5951409 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8095791500481 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8095791500481 / 8000000000000) = 1/(500000000000 / 8095791500481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2784491537 / 1000000000) (1392245771 / 500000000) (Real.log (8095791500481 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (8095791500481 / 500000000000) = -Real.log (500000000000 / 8095791500481) := by
    rw [show ((8095791500481 / 500000000000) : ℝ) = ((500000000000 / 8095791500481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (560126523 / 200000000) ≤ -Real.log (500000000000 / 8227526618957) ∧
    -Real.log (500000000000 / 8227526618957) ≤ (140031631 / 50000000) := by
  have h := checkLog_sound (w := (227526618957 / 16227526618957)) (n := 12)
    (lo := (5608779 / 200000000)) (hi := (3505487 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8227526618957 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(8227526618957 / 8000000000000) = 1/(500000000000 / 8227526618957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (560126523 / 200000000) (140031631 / 50000000) (Real.log (8227526618957 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (8227526618957 / 500000000000) = -Real.log (500000000000 / 8227526618957) := by
    rw [show ((8227526618957 / 500000000000) : ℝ) = ((500000000000 / 8227526618957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1359202629 / 500000000) ≤ -Real.log (250000000000 / 3789033217009) ∧
    -Real.log (250000000000 / 3789033217009) ≤ (1359202631 / 500000000) := by
  have h := checkLog_sound (w := (1789033217009 / 5789033217009)) (n := 12)
    (lo := (319481859 / 500000000)) (hi := (638963719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3789033217009 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3789033217009 / 2000000000000) = 1/(250000000000 / 3789033217009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1359202629 / 500000000) (1359202631 / 500000000) (Real.log (3789033217009 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (3789033217009 / 250000000000) = -Real.log (250000000000 / 3789033217009) := by
    rw [show ((3789033217009 / 250000000000) : ℝ) = ((250000000000 / 3789033217009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (547288181 / 200000000) ≤ -Real.log (500000000000 / 7715981727657) ∧
    -Real.log (500000000000 / 7715981727657) ≤ (2736440909 / 1000000000) := by
  have h := checkLog_sound (w := (3715981727657 / 11715981727657)) (n := 12)
    (lo := (131399873 / 200000000)) (hi := (328499683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7715981727657 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(7715981727657 / 4000000000000) = 1/(500000000000 / 7715981727657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (547288181 / 200000000) (2736440909 / 1000000000) (Real.log (7715981727657 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7715981727657 / 500000000000) = -Real.log (500000000000 / 7715981727657) := by
    rw [show ((7715981727657 / 500000000000) : ℝ) = ((500000000000 / 7715981727657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0190
