import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0068
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

theorem reflection_log_1_neg : (6773641 / 10000000) ≤ -Real.log (102400 / 201593) ∧
    -Real.log (102400 / 201593) ≤ (677364101 / 1000000000) := by
  have h := checkLog_sound (w := (99193 / 303993)) (n := 12)
    (lo := (6773641 / 10000000)) (hi := (677364101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201593 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201593 / 102400) = 1/(102400 / 201593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (6773641 / 10000000) (677364101 / 1000000000) (Real.log (201593 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (201593 / 102400) = -Real.log (102400 / 201593) := by
    rw [show ((201593 / 102400) : ℝ) = ((102400 / 201593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3463550789 / 1000000000) ≤ -Real.log (3207 / 102400) ∧
    -Real.log (3207 / 102400) ≤ (1731775397 / 500000000) := by
  have h := checkLog_sound (w := (3193 / 9607)) (n := 12)
    (lo := (690962069 / 1000000000)) (hi := (69096207 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 3207) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6400 / 3207) = 1/(3207 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1731775397 / 500000000) (-3463550789 / 1000000000) (Real.log (3207 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (677269847 / 1000000000) ≤ -Real.log (51200 / 100787) ∧
    -Real.log (51200 / 100787) ≤ (84658731 / 125000000) := by
  have h := checkLog_sound (w := (49587 / 151987)) (n := 12)
    (lo := (677269847 / 1000000000)) (hi := (84658731 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100787 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100787 / 51200) = 1/(51200 / 100787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (677269847 / 1000000000) (84658731 / 125000000) (Real.log (100787 / 51200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (100787 / 51200) = -Real.log (51200 / 100787) := by
    rw [show ((100787 / 51200) : ℝ) = ((51200 / 100787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (345764373 / 100000000) ≤ -Real.log (1613 / 51200) ∧
    -Real.log (1613 / 51200) ≤ (691528747 / 200000000) := by
  have h := checkLog_sound (w := (1587 / 4813)) (n := 12)
    (lo := (68505501 / 100000000)) (hi := (685055011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1613) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 1613) = 1/(1613 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-691528747 / 200000000) (-345764373 / 100000000) (Real.log (1613 / 51200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (132265583 / 200000000) ≤ -Real.log (51200 / 99193) ∧
    -Real.log (51200 / 99193) ≤ (165331979 / 250000000) := by
  have h := checkLog_sound (w := (47993 / 150393)) (n := 12)
    (lo := (132265583 / 200000000)) (hi := (165331979 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99193 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99193 / 51200) = 1/(51200 / 99193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (132265583 / 200000000) (165331979 / 250000000) (Real.log (99193 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (99193 / 51200) = -Real.log (51200 / 99193) := by
    rw [show ((99193 / 51200) : ℝ) = ((51200 / 99193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2770403609 / 1000000000) ≤ -Real.log (3207 / 51200) ∧
    -Real.log (3207 / 51200) ≤ (2770403613 / 1000000000) := by
  have h := checkLog_sound (w := (3193 / 9607)) (n := 12)
    (lo := (690962069 / 1000000000)) (hi := (69096207 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6400 / 3207) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6400 / 3207) = 1/(3207 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2770403613 / 1000000000) (-2770403609 / 1000000000) (Real.log (3207 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (661136351 / 1000000000) ≤ -Real.log (25600 / 49587) ∧
    -Real.log (25600 / 49587) ≤ (20660511 / 31250000) := by
  have h := checkLog_sound (w := (23987 / 75187)) (n := 12)
    (lo := (661136351 / 1000000000)) (hi := (20660511 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49587 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49587 / 25600) = 1/(25600 / 49587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (661136351 / 1000000000) (20660511 / 31250000) (Real.log (49587 / 25600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49587 / 25600) = -Real.log (25600 / 49587) := by
    rw [show ((49587 / 25600) : ℝ) = ((25600 / 49587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (55289931 / 20000000) ≤ -Real.log (1613 / 25600) ∧
    -Real.log (1613 / 25600) ≤ (1382248277 / 500000000) := by
  have h := checkLog_sound (w := (1587 / 4813)) (n := 12)
    (lo := (68505501 / 100000000)) (hi := (685055011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 1613) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 1613) = 1/(1613 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1382248277 / 500000000) (-55289931 / 20000000) (Real.log (1613 / 25600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (33996131 / 50000000) ≤ -Real.log (40000 / 78949) ∧
    -Real.log (40000 / 78949) ≤ (679922621 / 1000000000) := by
  have h := checkLog_sound (w := (38949 / 118949)) (n := 12)
    (lo := (33996131 / 50000000)) (hi := (679922621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78949 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78949 / 40000) = 1/(40000 / 78949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (33996131 / 50000000) (679922621 / 1000000000) (Real.log (78949 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (78949 / 40000) = -Real.log (40000 / 78949) := by
    rw [show ((78949 / 40000) : ℝ) = ((40000 / 78949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3639137359 / 1000000000) ≤ -Real.log (1051 / 40000) ∧
    -Real.log (1051 / 40000) ≤ (727827473 / 200000000) := by
  have h := checkLog_sound (w := (199 / 2301)) (n := 12)
    (lo := (173401459 / 1000000000)) (hi := (8670073 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1051) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1250 / 1051) = 1/(1051 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-727827473 / 200000000) (-3639137359 / 1000000000) (Real.log (1051 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (339998801 / 500000000) ≤ -Real.log (1000000 / 1973873) ∧
    -Real.log (1000000 / 1973873) ≤ (679997603 / 1000000000) := by
  have h := checkLog_sound (w := (973873 / 2973873)) (n := 12)
    (lo := (339998801 / 500000000)) (hi := (679997603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1973873 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1973873 / 1000000) = 1/(1000000 / 1973873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (339998801 / 500000000) (679997603 / 1000000000) (Real.log (1973873 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1973873 / 1000000) = -Real.log (1000000 / 1973873) := by
    rw [show ((1973873 / 1000000) : ℝ) = ((1000000 / 1973873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3644786013 / 1000000000) ≤ -Real.log (26127 / 1000000) ∧
    -Real.log (26127 / 1000000) ≤ (3644786019 / 1000000000) := by
  have h := checkLog_sound (w := (5123 / 57377)) (n := 12)
    (lo := (179050113 / 1000000000)) (hi := (89525057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26127) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 26127) = 1/(26127 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-3644786019 / 1000000000) (-3644786013 / 1000000000) (Real.log (26127 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (135967297 / 200000000) ≤ -Real.log (200000 / 394711) ∧
    -Real.log (200000 / 394711) ≤ (339918243 / 500000000) := by
  have h := checkLog_sound (w := (194711 / 594711)) (n := 12)
    (lo := (135967297 / 200000000)) (hi := (339918243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((394711 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(394711 / 200000) = 1/(200000 / 394711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (135967297 / 200000000) (339918243 / 500000000) (Real.log (394711 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (394711 / 200000) = -Real.log (200000 / 394711) := by
    rw [show ((394711 / 200000) : ℝ) = ((200000 / 394711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3632688171 / 1000000000) ≤ -Real.log (5289 / 200000) ∧
    -Real.log (5289 / 200000) ≤ (3632688177 / 1000000000) := by
  have h := checkLog_sound (w := (961 / 11539)) (n := 12)
    (lo := (166952271 / 1000000000)) (hi := (10434517 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5289) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(6250 / 5289) = 1/(5289 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3632688177 / 1000000000) (-3632688171 / 1000000000) (Real.log (5289 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (679912993 / 1000000000) ≤ -Real.log (500000 / 986853) ∧
    -Real.log (500000 / 986853) ≤ (339956497 / 500000000) := by
  have h := checkLog_sound (w := (486853 / 1486853)) (n := 12)
    (lo := (679912993 / 1000000000)) (hi := (339956497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((986853 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(986853 / 500000) = 1/(500000 / 986853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (679912993 / 1000000000) (339956497 / 500000000) (Real.log (986853 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (986853 / 500000) = -Real.log (500000 / 986853) := by
    rw [show ((986853 / 500000) : ℝ) = ((500000 / 986853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3638414499 / 1000000000) ≤ -Real.log (13147 / 500000) ∧
    -Real.log (13147 / 500000) ≤ (727682901 / 200000000) := by
  have h := checkLog_sound (w := (1239 / 14386)) (n := 12)
    (lo := (172678599 / 1000000000)) (hi := (863393 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13147) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 13147) = 1/(13147 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-727682901 / 200000000) (-3638414499 / 1000000000) (Real.log (13147 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4319059979 / 1000000000) ≤ -Real.log (250000000000 / 18779495718363) ∧
    -Real.log (250000000000 / 18779495718363) ≤ (2159529993 / 500000000) := by
  have h := checkLog_sound (w := (2779495718363 / 34779495718363)) (n := 12)
    (lo := (160176899 / 1000000000)) (hi := (1601769 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18779495718363 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(18779495718363 / 16000000000000) = 1/(250000000000 / 18779495718363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4319059979 / 1000000000) (2159529993 / 500000000) (Real.log (18779495718363 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (18779495718363 / 250000000000) = -Real.log (250000000000 / 18779495718363) := by
    rw [show ((18779495718363 / 250000000000) : ℝ) = ((250000000000 / 18779495718363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (864956723 / 200000000) ≤ -Real.log (250000000000 / 18887290925097) ∧
    -Real.log (250000000000 / 18887290925097) ≤ (2162391811 / 500000000) := by
  have h := checkLog_sound (w := (2887290925097 / 34887290925097)) (n := 12)
    (lo := (33180107 / 200000000)) (hi := (20737567 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18887290925097 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(18887290925097 / 16000000000000) = 1/(250000000000 / 18887290925097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (864956723 / 200000000) (2162391811 / 500000000) (Real.log (18887290925097 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (18887290925097 / 250000000000) = -Real.log (250000000000 / 18887290925097) := by
    rw [show ((18887290925097 / 250000000000) : ℝ) = ((250000000000 / 18887290925097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (269532791 / 62500000) ≤ -Real.log (62500000000 / 4664291453961) ∧
    -Real.log (62500000000 / 4664291453961) ≤ (4312524663 / 1000000000) := by
  have h := checkLog_sound (w := (664291453961 / 8664291453961)) (n := 12)
    (lo := (19205197 / 125000000)) (hi := (153641577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4664291453961 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(4664291453961 / 4000000000000) = 1/(62500000000 / 4664291453961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (269532791 / 62500000) (4312524663 / 1000000000) (Real.log (4664291453961 / 62500000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4664291453961 / 62500000000) = -Real.log (62500000000 / 4664291453961) := by
    rw [show ((4664291453961 / 62500000000) : ℝ) = ((62500000000 / 4664291453961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4318327493 / 1000000000) ≤ -Real.log (250000000000 / 18765745036891) ∧
    -Real.log (250000000000 / 18765745036891) ≤ (1727331 / 400000) := by
  have h := checkLog_sound (w := (2765745036891 / 34765745036891)) (n := 12)
    (lo := (159444413 / 1000000000)) (hi := (79722207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18765745036891 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(18765745036891 / 16000000000000) = 1/(250000000000 / 18765745036891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4318327493 / 1000000000) (1727331 / 400000) (Real.log (18765745036891 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (18765745036891 / 250000000000) = -Real.log (250000000000 / 18765745036891) := by
    rw [show ((18765745036891 / 250000000000) : ℝ) = ((250000000000 / 18765745036891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0068
