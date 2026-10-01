import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0200
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

theorem reflection_log_1_neg : (11842351 / 20000000) ≤ -Real.log (640 / 1157) ∧
    -Real.log (640 / 1157) ≤ (592117551 / 1000000000) := by
  have h := checkLog_sound (w := (517 / 1797)) (n := 12)
    (lo := (11842351 / 20000000)) (hi := (592117551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1157 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1157 / 640) = 1/(640 / 1157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11842351 / 20000000) (592117551 / 1000000000) (Real.log (1157 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1157 / 640) = -Real.log (640 / 1157) := by
    rw [show ((1157 / 640) : ℝ) = ((640 / 1157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1649283819 / 1000000000) ≤ -Real.log (123 / 640) ∧
    -Real.log (123 / 640) ≤ (824641911 / 500000000) := by
  have h := checkLog_sound (w := (37 / 283)) (n := 12)
    (lo := (262989459 / 1000000000)) (hi := (13149473 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 123) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 123) = 1/(123 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-824641911 / 500000000) (-1649283819 / 1000000000) (Real.log (123 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (588827789 / 1000000000) ≤ -Real.log (1600 / 2883) ∧
    -Real.log (1600 / 2883) ≤ (58882779 / 100000000) := by
  have h := checkLog_sound (w := (1283 / 4483)) (n := 12)
    (lo := (588827789 / 1000000000)) (hi := (58882779 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2883 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2883 / 1600) = 1/(1600 / 2883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (588827789 / 1000000000) (58882779 / 100000000) (Real.log (2883 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2883 / 1600) = -Real.log (1600 / 2883) := by
    rw [show ((2883 / 1600) : ℝ) = ((1600 / 2883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1618857133 / 1000000000) ≤ -Real.log (317 / 1600) ∧
    -Real.log (317 / 1600) ≤ (101178571 / 62500000) := by
  have h := checkLog_sound (w := (83 / 717)) (n := 12)
    (lo := (232562773 / 1000000000)) (hi := (116281387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 317) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 317) = 1/(317 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-101178571 / 62500000) (-1618857133 / 1000000000) (Real.log (317 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (239860939 / 500000000) ≤ -Real.log (320 / 517) ∧
    -Real.log (320 / 517) ≤ (479721879 / 1000000000) := by
  have h := checkLog_sound (w := (197 / 837)) (n := 12)
    (lo := (239860939 / 500000000)) (hi := (479721879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((517 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(517 / 320) = 1/(320 / 517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (239860939 / 500000000) (479721879 / 1000000000) (Real.log (517 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (517 / 320) = -Real.log (320 / 517) := by
    rw [show ((517 / 320) : ℝ) = ((320 / 517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (956136639 / 1000000000) ≤ -Real.log (123 / 320) ∧
    -Real.log (123 / 320) ≤ (956136641 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 283)) (n := 12)
    (lo := (262989459 / 1000000000)) (hi := (13149473 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 123) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(160 / 123) = 1/(123 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-956136641 / 1000000000) (-956136639 / 1000000000) (Real.log (123 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (118086159 / 250000000) ≤ -Real.log (800 / 1283) ∧
    -Real.log (800 / 1283) ≤ (472344637 / 1000000000) := by
  have h := checkLog_sound (w := (483 / 2083)) (n := 12)
    (lo := (118086159 / 250000000)) (hi := (472344637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1283 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1283 / 800) = 1/(800 / 1283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (118086159 / 250000000) (472344637 / 1000000000) (Real.log (1283 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1283 / 800) = -Real.log (800 / 1283) := by
    rw [show ((1283 / 800) : ℝ) = ((800 / 1283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (925709953 / 1000000000) ≤ -Real.log (317 / 800) ∧
    -Real.log (317 / 800) ≤ (185141991 / 200000000) := by
  have h := checkLog_sound (w := (83 / 717)) (n := 12)
    (lo := (232562773 / 1000000000)) (hi := (116281387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 317) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 317) = 1/(317 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-185141991 / 200000000) (-925709953 / 1000000000) (Real.log (317 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (15563383 / 25000000) ≤ -Real.log (1000000 / 1863647) ∧
    -Real.log (1000000 / 1863647) ≤ (622535321 / 1000000000) := by
  have h := checkLog_sound (w := (863647 / 2863647)) (n := 12)
    (lo := (15563383 / 25000000)) (hi := (622535321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1863647 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1863647 / 1000000) = 1/(1000000 / 1863647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (15563383 / 25000000) (622535321 / 1000000000) (Real.log (1863647 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1863647 / 1000000) = -Real.log (1000000 / 1863647) := by
    rw [show ((1863647 / 1000000) : ℝ) = ((1000000 / 1863647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (996254083 / 500000000) ≤ -Real.log (136353 / 1000000) ∧
    -Real.log (136353 / 1000000) ≤ (1992508169 / 1000000000) := by
  have h := checkLog_sound (w := (113647 / 386353)) (n := 12)
    (lo := (303106903 / 500000000)) (hi := (606213807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 136353) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 136353) = 1/(136353 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1992508169 / 1000000000) (-996254083 / 500000000) (Real.log (136353 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (312125991 / 500000000) ≤ -Real.log (1000000 / 1866849) ∧
    -Real.log (1000000 / 1866849) ≤ (624251983 / 1000000000) := by
  have h := checkLog_sound (w := (866849 / 2866849)) (n := 12)
    (lo := (312125991 / 500000000)) (hi := (624251983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1866849 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1866849 / 1000000) = 1/(1000000 / 1866849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (312125991 / 500000000) (624251983 / 1000000000) (Real.log (1866849 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1866849 / 1000000) = -Real.log (1000000 / 1866849) := by
    rw [show ((1866849 / 1000000) : ℝ) = ((1000000 / 1866849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (403254291 / 200000000) ≤ -Real.log (133151 / 1000000) ∧
    -Real.log (133151 / 1000000) ≤ (1008135729 / 500000000) := by
  have h := checkLog_sound (w := (116849 / 383151)) (n := 12)
    (lo := (125995419 / 200000000)) (hi := (78747137 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 133151) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 133151) = 1/(133151 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1008135729 / 500000000) (-403254291 / 200000000) (Real.log (133151 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (616063631 / 1000000000) ≤ -Real.log (8000 / 14813) ∧
    -Real.log (8000 / 14813) ≤ (38503977 / 62500000) := by
  have h := checkLog_sound (w := (6813 / 22813)) (n := 12)
    (lo := (616063631 / 1000000000)) (hi := (38503977 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14813 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14813 / 8000) = 1/(8000 / 14813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (616063631 / 1000000000) (38503977 / 62500000) (Real.log (14813 / 8000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (14813 / 8000) = -Real.log (8000 / 14813) := by
    rw [show ((14813 / 8000) : ℝ) = ((8000 / 14813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (238501553 / 125000000) ≤ -Real.log (1187 / 8000) ∧
    -Real.log (1187 / 8000) ≤ (1908012427 / 1000000000) := by
  have h := checkLog_sound (w := (813 / 3187)) (n := 12)
    (lo := (32607379 / 62500000)) (hi := (104343613 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1187) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2000 / 1187) = 1/(1187 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1908012427 / 1000000000) (-238501553 / 125000000) (Real.log (1187 / 8000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (618252283 / 1000000000) ≤ -Real.log (500000 / 927841) ∧
    -Real.log (500000 / 927841) ≤ (154563071 / 250000000) := by
  have h := checkLog_sound (w := (427841 / 1427841)) (n := 12)
    (lo := (618252283 / 1000000000)) (hi := (154563071 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((927841 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(927841 / 500000) = 1/(500000 / 927841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (618252283 / 1000000000) (154563071 / 250000000) (Real.log (927841 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (927841 / 500000) = -Real.log (500000 / 927841) := by
    rw [show ((927841 / 500000) : ℝ) = ((500000 / 927841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1935736079 / 1000000000) ≤ -Real.log (72159 / 500000) ∧
    -Real.log (72159 / 500000) ≤ (967868041 / 500000000) := by
  have h := checkLog_sound (w := (52841 / 197159)) (n := 12)
    (lo := (549441719 / 1000000000)) (hi := (13736043 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 72159) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 72159) = 1/(72159 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-967868041 / 500000000) (-1935736079 / 1000000000) (Real.log (72159 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1307521743 / 500000000) ≤ -Real.log (15625000000 / 213559543061) ∧
    -Real.log (15625000000 / 213559543061) ≤ (261504349 / 100000000) := by
  have h := checkLog_sound (w := (88559543061 / 338559543061)) (n := 12)
    (lo := (267800973 / 500000000)) (hi := (535601947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((213559543061 / 125000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(213559543061 / 125000000000) = 1/(15625000000 / 213559543061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1307521743 / 500000000) (261504349 / 100000000) (Real.log (213559543061 / 15625000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (213559543061 / 15625000000) = -Real.log (15625000000 / 213559543061) := by
    rw [show ((213559543061 / 15625000000) : ℝ) = ((15625000000 / 213559543061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2640523437 / 1000000000) ≤ -Real.log (125000000000 / 1752567573657) ∧
    -Real.log (125000000000 / 1752567573657) ≤ (2640523441 / 1000000000) := by
  have h := checkLog_sound (w := (752567573657 / 2752567573657)) (n := 12)
    (lo := (561081897 / 1000000000)) (hi := (280540949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1752567573657 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1752567573657 / 1000000000000) = 1/(125000000000 / 1752567573657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2640523437 / 1000000000) (2640523441 / 1000000000) (Real.log (1752567573657 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1752567573657 / 125000000000) = -Real.log (125000000000 / 1752567573657) := by
    rw [show ((1752567573657 / 125000000000) : ℝ) = ((125000000000 / 1752567573657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (315509507 / 125000000) ≤ -Real.log (250000000000 / 3119839932603) ∧
    -Real.log (250000000000 / 3119839932603) ≤ (126203803 / 50000000) := by
  have h := checkLog_sound (w := (1119839932603 / 5119839932603)) (n := 12)
    (lo := (111158629 / 250000000)) (hi := (444634517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3119839932603 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3119839932603 / 2000000000000) = 1/(250000000000 / 3119839932603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (315509507 / 125000000) (126203803 / 50000000) (Real.log (3119839932603 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (3119839932603 / 250000000000) = -Real.log (250000000000 / 3119839932603) := by
    rw [show ((3119839932603 / 250000000000) : ℝ) = ((250000000000 / 3119839932603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1276994181 / 500000000) ≤ -Real.log (500000000000 / 6429142587897) ∧
    -Real.log (500000000000 / 6429142587897) ≤ (1276994183 / 500000000) := by
  have h := checkLog_sound (w := (2429142587897 / 10429142587897)) (n := 12)
    (lo := (237273411 / 500000000)) (hi := (474546823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6429142587897 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6429142587897 / 4000000000000) = 1/(500000000000 / 6429142587897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1276994181 / 500000000) (1276994183 / 500000000) (Real.log (6429142587897 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (6429142587897 / 500000000000) = -Real.log (500000000000 / 6429142587897) := by
    rw [show ((6429142587897 / 500000000000) : ℝ) = ((500000000000 / 6429142587897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0200
