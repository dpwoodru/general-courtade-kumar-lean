import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0169
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

theorem reflection_log_1_neg : (127728299 / 200000000) ≤ -Real.log (6400 / 12121) ∧
    -Real.log (6400 / 12121) ≤ (79830187 / 125000000) := by
  have h := checkLog_sound (w := (5721 / 18521)) (n := 12)
    (lo := (127728299 / 200000000)) (hi := (79830187 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12121 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12121 / 6400) = 1/(6400 / 12121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (127728299 / 200000000) (79830187 / 125000000) (Real.log (12121 / 6400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12121 / 6400) = -Real.log (6400 / 12121) := by
    rw [show ((12121 / 6400) : ℝ) = ((6400 / 12121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (112171607 / 50000000) ≤ -Real.log (679 / 6400) ∧
    -Real.log (679 / 6400) ≤ (140214509 / 62500000) := by
  have h := checkLog_sound (w := (121 / 1479)) (n := 12)
    (lo := (819953 / 5000000)) (hi := (163990601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 679) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 679) = 1/(679 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-140214509 / 62500000) (-112171607 / 50000000) (Real.log (679 / 6400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (39866089 / 62500000) ≤ -Real.log (12800 / 24223) ∧
    -Real.log (12800 / 24223) ≤ (25514297 / 40000000) := by
  have h := checkLog_sound (w := (11423 / 37023)) (n := 12)
    (lo := (39866089 / 62500000)) (hi := (25514297 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24223 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24223 / 12800) = 1/(12800 / 24223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (39866089 / 62500000) (25514297 / 40000000) (Real.log (24223 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24223 / 12800) = -Real.log (12800 / 24223) := by
    rw [show ((24223 / 12800) : ℝ) = ((12800 / 24223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (2229537949 / 1000000000) ≤ -Real.log (1377 / 12800) ∧
    -Real.log (1377 / 12800) ≤ (2229537953 / 1000000000) := by
  have h := checkLog_sound (w := (223 / 2977)) (n := 12)
    (lo := (150096409 / 1000000000)) (hi := (15009641 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1377) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1377) = 1/(1377 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-2229537953 / 1000000000) (-2229537949 / 1000000000) (Real.log (1377 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (116198561 / 200000000) ≤ -Real.log (3200 / 5721) ∧
    -Real.log (3200 / 5721) ≤ (290496403 / 500000000) := by
  have h := checkLog_sound (w := (2521 / 8921)) (n := 12)
    (lo := (116198561 / 200000000)) (hi := (290496403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5721 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5721 / 3200) = 1/(3200 / 5721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (116198561 / 200000000) (290496403 / 500000000) (Real.log (5721 / 3200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (5721 / 3200) = -Real.log (3200 / 5721) := by
    rw [show ((5721 / 3200) : ℝ) = ((3200 / 5721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (9689281 / 6250000) ≤ -Real.log (679 / 3200) ∧
    -Real.log (679 / 3200) ≤ (1550284963 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 1479)) (n := 12)
    (lo := (819953 / 5000000)) (hi := (163990601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 679) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 679) = 1/(679 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1550284963 / 1000000000) (-9689281 / 6250000) (Real.log (679 / 3200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (144832719 / 250000000) ≤ -Real.log (6400 / 11423) ∧
    -Real.log (6400 / 11423) ≤ (579330877 / 1000000000) := by
  have h := checkLog_sound (w := (5023 / 17823)) (n := 12)
    (lo := (144832719 / 250000000)) (hi := (579330877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11423 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11423 / 6400) = 1/(6400 / 11423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (144832719 / 250000000) (579330877 / 1000000000) (Real.log (11423 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11423 / 6400) = -Real.log (6400 / 11423) := by
    rw [show ((11423 / 6400) : ℝ) = ((6400 / 11423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1536390769 / 1000000000) ≤ -Real.log (1377 / 6400) ∧
    -Real.log (1377 / 6400) ≤ (384097693 / 250000000) := by
  have h := checkLog_sound (w := (223 / 2977)) (n := 12)
    (lo := (150096409 / 1000000000)) (hi := (15009641 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1377) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1377) = 1/(1377 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-384097693 / 250000000) (-1536390769 / 1000000000) (Real.log (1377 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (325707177 / 500000000) ≤ -Real.log (250000 / 479563) ∧
    -Real.log (250000 / 479563) ≤ (130282871 / 200000000) := by
  have h := checkLog_sound (w := (229563 / 729563)) (n := 12)
    (lo := (325707177 / 500000000)) (hi := (130282871 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((479563 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(479563 / 250000) = 1/(250000 / 479563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (325707177 / 500000000) (130282871 / 200000000) (Real.log (479563 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (479563 / 250000) = -Real.log (250000 / 479563) := by
    rw [show ((479563 / 250000) : ℝ) = ((250000 / 479563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (626028483 / 250000000) ≤ -Real.log (20437 / 250000) ∧
    -Real.log (20437 / 250000) ≤ (156507121 / 62500000) := by
  have h := checkLog_sound (w := (10813 / 51687)) (n := 12)
    (lo := (53084049 / 125000000)) (hi := (424672393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20437) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 20437) = 1/(20437 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-156507121 / 62500000) (-626028483 / 250000000) (Real.log (20437 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (162983621 / 250000000) ≤ -Real.log (4000 / 7677) ∧
    -Real.log (4000 / 7677) ≤ (130386897 / 200000000) := by
  have h := checkLog_sound (w := (3677 / 11677)) (n := 12)
    (lo := (162983621 / 250000000)) (hi := (130386897 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7677 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7677 / 4000) = 1/(4000 / 7677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (162983621 / 250000000) (130386897 / 200000000) (Real.log (7677 / 4000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (7677 / 4000) = -Real.log (4000 / 7677) := by
    rw [show ((7677 / 4000) : ℝ) = ((4000 / 7677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (503279463 / 200000000) ≤ -Real.log (323 / 4000) ∧
    -Real.log (323 / 4000) ≤ (2516397319 / 1000000000) := by
  have h := checkLog_sound (w := (177 / 823)) (n := 12)
    (lo := (17478231 / 40000000)) (hi := (3413717 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 323) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(500 / 323) = 1/(323 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2516397319 / 1000000000) (-503279463 / 200000000) (Real.log (323 / 4000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (649949971 / 1000000000) ≤ -Real.log (200000 / 383089) ∧
    -Real.log (200000 / 383089) ≤ (162487493 / 250000000) := by
  have h := checkLog_sound (w := (183089 / 583089)) (n := 12)
    (lo := (649949971 / 1000000000)) (hi := (162487493 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383089 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(383089 / 200000) = 1/(200000 / 383089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (649949971 / 1000000000) (162487493 / 250000000) (Real.log (383089 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (383089 / 200000) = -Real.log (200000 / 383089) := by
    rw [show ((383089 / 200000) : ℝ) = ((200000 / 383089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2470353067 / 1000000000) ≤ -Real.log (16911 / 200000) ∧
    -Real.log (16911 / 200000) ≤ (2470353071 / 1000000000) := by
  have h := checkLog_sound (w := (8089 / 41911)) (n := 12)
    (lo := (390911527 / 1000000000)) (hi := (48863941 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 16911) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 16911) = 1/(16911 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-2470353071 / 1000000000) (-2470353067 / 1000000000) (Real.log (16911 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (10164341 / 15625000) ≤ -Real.log (1000000 / 1916533) ∧
    -Real.log (1000000 / 1916533) ≤ (26020713 / 40000000) := by
  have h := checkLog_sound (w := (916533 / 2916533)) (n := 12)
    (lo := (10164341 / 15625000)) (hi := (26020713 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1916533 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1916533 / 1000000) = 1/(1000000 / 1916533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (10164341 / 15625000) (26020713 / 40000000) (Real.log (1916533 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1916533 / 1000000) = -Real.log (1000000 / 1916533) := by
    rw [show ((1916533 / 1000000) : ℝ) = ((1000000 / 1916533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (2483303933 / 1000000000) ≤ -Real.log (83467 / 1000000) ∧
    -Real.log (83467 / 1000000) ≤ (2483303937 / 1000000000) := by
  have h := checkLog_sound (w := (41533 / 208467)) (n := 12)
    (lo := (403862393 / 1000000000)) (hi := (201931197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 83467) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 83467) = 1/(83467 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-2483303937 / 1000000000) (-2483303933 / 1000000000) (Real.log (83467 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1577764143 / 500000000) ≤ -Real.log (500000000000 / 11732715173459) ∧
    -Real.log (500000000000 / 11732715173459) ≤ (3155528291 / 1000000000) := by
  have h := checkLog_sound (w := (3732715173459 / 19732715173459)) (n := 12)
    (lo := (191469783 / 500000000)) (hi := (382939567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11732715173459 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11732715173459 / 8000000000000) = 1/(500000000000 / 11732715173459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1577764143 / 500000000) (3155528291 / 1000000000) (Real.log (11732715173459 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (11732715173459 / 500000000000) = -Real.log (500000000000 / 11732715173459) := by
    rw [show ((11732715173459 / 500000000000) : ℝ) = ((500000000000 / 11732715173459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3168331799 / 1000000000) ≤ -Real.log (500000000000 / 11883900928793) ∧
    -Real.log (500000000000 / 11883900928793) ≤ (792082951 / 250000000) := by
  have h := checkLog_sound (w := (3883900928793 / 19883900928793)) (n := 12)
    (lo := (395743079 / 1000000000)) (hi := (9893577 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11883900928793 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(11883900928793 / 8000000000000) = 1/(500000000000 / 11883900928793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3168331799 / 1000000000) (792082951 / 250000000) (Real.log (11883900928793 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (11883900928793 / 500000000000) = -Real.log (500000000000 / 11883900928793) := by
    rw [show ((11883900928793 / 500000000000) : ℝ) = ((500000000000 / 11883900928793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1560151519 / 500000000) ≤ -Real.log (7812500000 / 176978464461) ∧
    -Real.log (7812500000 / 176978464461) ≤ (3120303043 / 1000000000) := by
  have h := checkLog_sound (w := (51978464461 / 301978464461)) (n := 12)
    (lo := (173857159 / 500000000)) (hi := (347714319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((176978464461 / 125000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(176978464461 / 125000000000) = 1/(7812500000 / 176978464461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1560151519 / 500000000) (3120303043 / 1000000000) (Real.log (176978464461 / 7812500000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (176978464461 / 7812500000) = -Real.log (7812500000 / 176978464461) := by
    rw [show ((176978464461 / 7812500000) : ℝ) = ((7812500000 / 176978464461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (3133821757 / 1000000000) ≤ -Real.log (10000000000 / 229615656487) ∧
    -Real.log (10000000000 / 229615656487) ≤ (1566910881 / 500000000) := by
  have h := checkLog_sound (w := (69615656487 / 389615656487)) (n := 12)
    (lo := (361233037 / 1000000000)) (hi := (180616519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229615656487 / 160000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(229615656487 / 160000000000) = 1/(10000000000 / 229615656487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (3133821757 / 1000000000) (1566910881 / 500000000) (Real.log (229615656487 / 10000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (229615656487 / 10000000000) = -Real.log (10000000000 / 229615656487) := by
    rw [show ((229615656487 / 10000000000) : ℝ) = ((10000000000 / 229615656487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0169
