import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0063
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

theorem reflection_log_1_neg : (363991859 / 1000000000) ≤ -Real.log (640 / 921) ∧
    -Real.log (640 / 921) ≤ (18199593 / 50000000) := by
  have h := checkLog_sound (w := (281 / 1561)) (n := 12)
    (lo := (363991859 / 1000000000)) (hi := (18199593 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((921 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(921 / 640) = 1/(640 / 921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (363991859 / 1000000000) (18199593 / 50000000) (Real.log (921 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (921 / 640) = -Real.log (640 / 921) := by
    rw [show ((921 / 640) : ℝ) = ((640 / 921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (578145787 / 1000000000) ≤ -Real.log (359 / 640) ∧
    -Real.log (359 / 640) ≤ (144536447 / 250000000) := by
  have h := checkLog_sound (w := (281 / 999)) (n := 12)
    (lo := (578145787 / 1000000000)) (hi := (144536447 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 359) = 1/(359 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-144536447 / 250000000) (-578145787 / 1000000000) (Real.log (359 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (72635439 / 200000000) ≤ -Real.log (2560 / 3681) ∧
    -Real.log (2560 / 3681) ≤ (90794299 / 250000000) := by
  have h := checkLog_sound (w := (1121 / 6241)) (n := 12)
    (lo := (72635439 / 200000000)) (hi := (90794299 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3681 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3681 / 2560) = 1/(2560 / 3681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (72635439 / 200000000) (90794299 / 250000000) (Real.log (3681 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3681 / 2560) = -Real.log (2560 / 3681) := by
    rw [show ((3681 / 2560) : ℝ) = ((2560 / 3681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (57605883 / 100000000) ≤ -Real.log (1439 / 2560) ∧
    -Real.log (1439 / 2560) ≤ (576058831 / 1000000000) := by
  have h := checkLog_sound (w := (1121 / 3999)) (n := 12)
    (lo := (57605883 / 100000000)) (hi := (576058831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1439) = 1/(1439 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-576058831 / 1000000000) (-57605883 / 100000000) (Real.log (1439 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (315136969 / 500000000) ≤ -Real.log (320 / 601) ∧
    -Real.log (320 / 601) ≤ (630273939 / 1000000000) := by
  have h := checkLog_sound (w := (281 / 921)) (n := 12)
    (lo := (315136969 / 500000000)) (hi := (630273939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((601 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(601 / 320) = 1/(320 / 601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (315136969 / 500000000) (630273939 / 1000000000) (Real.log (601 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (601 / 320) = -Real.log (320 / 601) := by
    rw [show ((601 / 320) : ℝ) = ((320 / 601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2104759347 / 1000000000) ≤ -Real.log (39 / 320) ∧
    -Real.log (39 / 320) ≤ (2104759351 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 79)) (n := 12)
    (lo := (25317807 / 1000000000)) (hi := (1582363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 39) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(40 / 39) = 1/(39 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2104759351 / 1000000000) (-2104759347 / 1000000000) (Real.log (39 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (629025239 / 1000000000) ≤ -Real.log (1280 / 2401) ∧
    -Real.log (1280 / 2401) ≤ (15725631 / 25000000) := by
  have h := checkLog_sound (w := (1121 / 3681)) (n := 12)
    (lo := (629025239 / 1000000000)) (hi := (15725631 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2401 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2401 / 1280) = 1/(1280 / 2401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (629025239 / 1000000000) (15725631 / 25000000) (Real.log (2401 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2401 / 1280) = -Real.log (1280 / 2401) := by
    rw [show ((2401 / 1280) : ℝ) = ((1280 / 2401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2085711153 / 1000000000) ≤ -Real.log (159 / 1280) ∧
    -Real.log (159 / 1280) ≤ (2085711157 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 319)) (n := 12)
    (lo := (6269613 / 1000000000)) (hi := (3134807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 159) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 159) = 1/(159 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2085711157 / 1000000000) (-2085711153 / 1000000000) (Real.log (159 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (250694519 / 500000000) ≤ -Real.log (1000000 / 1651013) ∧
    -Real.log (1000000 / 1651013) ≤ (501389039 / 1000000000) := by
  have h := checkLog_sound (w := (651013 / 2651013)) (n := 12)
    (lo := (250694519 / 500000000)) (hi := (501389039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1651013 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1651013 / 1000000) = 1/(1000000 / 1651013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (250694519 / 500000000) (501389039 / 1000000000) (Real.log (1651013 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1651013 / 1000000) = -Real.log (1000000 / 1651013) := by
    rw [show ((1651013 / 1000000) : ℝ) = ((1000000 / 1651013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (526360303 / 500000000) ≤ -Real.log (348987 / 1000000) ∧
    -Real.log (348987 / 1000000) ≤ (32897519 / 31250000) := by
  have h := checkLog_sound (w := (151013 / 848987)) (n := 12)
    (lo := (179786713 / 500000000)) (hi := (359573427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 348987) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 348987) = 1/(348987 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-32897519 / 31250000) (-526360303 / 500000000) (Real.log (348987 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (100526107 / 200000000) ≤ -Real.log (125000 / 206633) ∧
    -Real.log (125000 / 206633) ≤ (62828817 / 125000000) := by
  have h := checkLog_sound (w := (81633 / 331633)) (n := 12)
    (lo := (100526107 / 200000000)) (hi := (62828817 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((206633 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(206633 / 125000) = 1/(125000 / 206633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (100526107 / 200000000) (62828817 / 125000000) (Real.log (206633 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (206633 / 125000) = -Real.log (125000 / 206633) := by
    rw [show ((206633 / 125000) : ℝ) = ((125000 / 206633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1058614953 / 1000000000) ≤ -Real.log (43367 / 125000) ∧
    -Real.log (43367 / 125000) ≤ (211722991 / 200000000) := by
  have h := checkLog_sound (w := (19133 / 105867)) (n := 12)
    (lo := (365467773 / 1000000000)) (hi := (182733887 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43367) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 43367) = 1/(43367 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-211722991 / 200000000) (-1058614953 / 1000000000) (Real.log (43367 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (52405879 / 125000000) ≤ -Real.log (62500 / 95051) ∧
    -Real.log (62500 / 95051) ≤ (419247033 / 1000000000) := by
  have h := checkLog_sound (w := (32551 / 157551)) (n := 12)
    (lo := (52405879 / 125000000)) (hi := (419247033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95051 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(95051 / 62500) = 1/(62500 / 95051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (52405879 / 125000000) (419247033 / 1000000000) (Real.log (95051 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (95051 / 62500) = -Real.log (62500 / 95051) := by
    rw [show ((95051 / 62500) : ℝ) = ((62500 / 95051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (735670621 / 1000000000) ≤ -Real.log (29949 / 62500) ∧
    -Real.log (29949 / 62500) ≤ (735670623 / 1000000000) := by
  have h := checkLog_sound (w := (1301 / 61199)) (n := 12)
    (lo := (42523441 / 1000000000)) (hi := (21261721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 29949) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 29949) = 1/(29949 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-735670623 / 1000000000) (-735670621 / 1000000000) (Real.log (29949 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (84120787 / 200000000) ≤ -Real.log (1000000 / 1522881) ∧
    -Real.log (1000000 / 1522881) ≤ (13143873 / 31250000) := by
  have h := checkLog_sound (w := (522881 / 2522881)) (n := 12)
    (lo := (84120787 / 200000000)) (hi := (13143873 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1522881 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1522881 / 1000000) = 1/(1000000 / 1522881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (84120787 / 200000000) (13143873 / 31250000) (Real.log (1522881 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1522881 / 1000000) = -Real.log (1000000 / 1522881) := by
    rw [show ((1522881 / 1000000) : ℝ) = ((1000000 / 1522881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (369994671 / 500000000) ≤ -Real.log (477119 / 1000000) ∧
    -Real.log (477119 / 1000000) ≤ (23124667 / 31250000) := by
  have h := checkLog_sound (w := (22881 / 977119)) (n := 12)
    (lo := (23421081 / 500000000)) (hi := (46842163 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 477119) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 477119) = 1/(477119 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-23124667 / 31250000) (-369994671 / 500000000) (Real.log (477119 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (388527411 / 250000000) ≤ -Real.log (500000000000 / 2365436248341) ∧
    -Real.log (500000000000 / 2365436248341) ≤ (1554109647 / 1000000000) := by
  have h := checkLog_sound (w := (365436248341 / 4365436248341)) (n := 12)
    (lo := (41953821 / 250000000)) (hi := (33563057 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2365436248341 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2365436248341 / 2000000000000) = 1/(500000000000 / 2365436248341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (388527411 / 250000000) (1554109647 / 1000000000) (Real.log (2365436248341 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2365436248341 / 500000000000) = -Real.log (500000000000 / 2365436248341) := by
    rw [show ((2365436248341 / 500000000000) : ℝ) = ((500000000000 / 2365436248341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (97577843 / 62500000) ≤ -Real.log (100000000000 / 476475200037) ∧
    -Real.log (100000000000 / 476475200037) ≤ (1561245491 / 1000000000) := by
  have h := checkLog_sound (w := (76475200037 / 876475200037)) (n := 12)
    (lo := (21868891 / 125000000)) (hi := (174951129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((476475200037 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(476475200037 / 400000000000) = 1/(100000000000 / 476475200037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (97577843 / 62500000) (1561245491 / 1000000000) (Real.log (476475200037 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (476475200037 / 100000000000) = -Real.log (100000000000 / 476475200037) := by
    rw [show ((476475200037 / 100000000000) : ℝ) = ((100000000000 / 476475200037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (577458827 / 500000000) ≤ -Real.log (250000000000 / 793440515543) ∧
    -Real.log (250000000000 / 793440515543) ≤ (144364707 / 125000000) := by
  have h := checkLog_sound (w := (293440515543 / 1293440515543)) (n := 12)
    (lo := (230885237 / 500000000)) (hi := (18470819 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((793440515543 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(793440515543 / 500000000000) = 1/(250000000000 / 793440515543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (577458827 / 500000000) (144364707 / 125000000) (Real.log (793440515543 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (793440515543 / 250000000000) = -Real.log (250000000000 / 793440515543) := by
    rw [show ((793440515543 / 250000000000) : ℝ) = ((250000000000 / 793440515543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (580296639 / 500000000) ≤ -Real.log (500000000000 / 1595913178893) ∧
    -Real.log (500000000000 / 1595913178893) ≤ (1813427 / 1562500) := by
  have h := checkLog_sound (w := (595913178893 / 2595913178893)) (n := 12)
    (lo := (233723049 / 500000000)) (hi := (467446099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1595913178893 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1595913178893 / 1000000000000) = 1/(500000000000 / 1595913178893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (580296639 / 500000000) (1813427 / 1562500) (Real.log (1595913178893 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1595913178893 / 500000000000) = -Real.log (500000000000 / 1595913178893) := by
    rw [show ((1595913178893 / 500000000000) : ℝ) = ((500000000000 / 1595913178893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0063
