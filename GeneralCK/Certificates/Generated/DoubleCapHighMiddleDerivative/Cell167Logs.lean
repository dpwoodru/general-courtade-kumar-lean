import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell167
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (149473257 / 500000000) ≤ -Real.log (640 / 863) ∧
    -Real.log (640 / 863) ≤ (59789303 / 200000000) := by
  have h := checkLog_sound (w := (223 / 1503)) (n := 12)
    (lo := (149473257 / 500000000)) (hi := (59789303 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((863 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(863 / 640) = 1/(640 / 863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (149473257 / 500000000) (59789303 / 200000000) (Real.log (863 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (863 / 640) = -Real.log (640 / 863) := by
    rw [show ((863 / 640) : ℝ) = ((640 / 863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (214190977 / 500000000) ≤ -Real.log (417 / 640) ∧
    -Real.log (417 / 640) ≤ (85676391 / 200000000) := by
  have h := checkLog_sound (w := (223 / 1057)) (n := 12)
    (lo := (214190977 / 500000000)) (hi := (85676391 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 417) = 1/(417 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-85676391 / 200000000) (-214190977 / 500000000) (Real.log (417 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (298511889 / 1000000000) ≤ -Real.log (5120 / 6901) ∧
    -Real.log (5120 / 6901) ≤ (29851189 / 100000000) := by
  have h := checkLog_sound (w := (1781 / 12021)) (n := 12)
    (lo := (298511889 / 1000000000)) (hi := (29851189 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6901 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6901 / 5120) = 1/(5120 / 6901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (298511889 / 1000000000) (29851189 / 100000000) (Real.log (6901 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6901 / 5120) = -Real.log (5120 / 6901) := by
    rw [show ((6901 / 5120) : ℝ) = ((5120 / 6901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (213741539 / 500000000) ≤ -Real.log (3339 / 5120) ∧
    -Real.log (3339 / 5120) ≤ (427483079 / 1000000000) := by
  have h := checkLog_sound (w := (1781 / 8459)) (n := 12)
    (lo := (213741539 / 500000000)) (hi := (427483079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3339) = 1/(3339 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-427483079 / 1000000000) (-213741539 / 500000000) (Real.log (3339 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (220960369 / 1000000000) ≤ -Real.log (500000 / 623637) ∧
    -Real.log (500000 / 623637) ≤ (22096037 / 100000000) := by
  have h := checkLog_sound (w := (123637 / 1123637)) (n := 12)
    (lo := (220960369 / 1000000000)) (hi := (22096037 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((623637 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(623637 / 500000) = 1/(500000 / 623637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (220960369 / 1000000000) (22096037 / 100000000) (Real.log (623637 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (623637 / 500000) = -Real.log (500000 / 623637) := by
    rw [show ((623637 / 500000) : ℝ) = ((500000 / 623637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (56810799 / 200000000) ≤ -Real.log (376363 / 500000) ∧
    -Real.log (376363 / 500000) ≤ (71013499 / 250000000) := by
  have h := checkLog_sound (w := (123637 / 876363)) (n := 12)
    (lo := (56810799 / 200000000)) (hi := (71013499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 376363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 376363) = 1/(376363 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-71013499 / 250000000) (-56810799 / 200000000) (Real.log (376363 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (4425973 / 20000000) ≤ -Real.log (62500 / 77981) ∧
    -Real.log (62500 / 77981) ≤ (221298651 / 1000000000) := by
  have h := checkLog_sound (w := (15481 / 140481)) (n := 12)
    (lo := (4425973 / 20000000)) (hi := (221298651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77981 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77981 / 62500) = 1/(62500 / 77981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (4425973 / 20000000) (221298651 / 1000000000) (Real.log (77981 / 62500)) := by
  have h := reflection_log_7_neg
  have he : Real.log (77981 / 62500) = -Real.log (62500 / 77981) := by
    rw [show ((77981 / 62500) : ℝ) = ((62500 / 77981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (284614781 / 1000000000) ≤ -Real.log (47019 / 62500) ∧
    -Real.log (47019 / 62500) ≤ (142307391 / 500000000) := by
  have h := checkLog_sound (w := (15481 / 109519)) (n := 12)
    (lo := (284614781 / 1000000000)) (hi := (142307391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 47019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 47019) = 1/(47019 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-142307391 / 500000000) (-284614781 / 1000000000) (Real.log (47019 / 62500)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (16370093 / 100000000) ≤ -Real.log (500000 / 588931) ∧
    -Real.log (500000 / 588931) ≤ (163700931 / 1000000000) := by
  have h := checkLog_sound (w := (88931 / 1088931)) (n := 12)
    (lo := (16370093 / 100000000)) (hi := (163700931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588931 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588931 / 500000) = 1/(500000 / 588931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (16370093 / 100000000) (163700931 / 1000000000) (Real.log (588931 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (588931 / 500000) = -Real.log (500000 / 588931) := by
    rw [show ((588931 / 500000) : ℝ) = ((500000 / 588931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (97923507 / 500000000) ≤ -Real.log (411069 / 500000) ∧
    -Real.log (411069 / 500000) ≤ (39169403 / 200000000) := by
  have h := checkLog_sound (w := (88931 / 911069)) (n := 12)
    (lo := (97923507 / 500000000)) (hi := (39169403 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 411069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 411069) = 1/(411069 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-39169403 / 200000000) (-97923507 / 500000000) (Real.log (411069 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (163967479 / 1000000000) ≤ -Real.log (15625 / 18409) ∧
    -Real.log (15625 / 18409) ≤ (4099187 / 25000000) := by
  have h := checkLog_sound (w := (1392 / 17017)) (n := 12)
    (lo := (163967479 / 1000000000)) (hi := (4099187 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18409 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18409 / 15625) = 1/(15625 / 18409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (163967479 / 1000000000) (4099187 / 25000000) (Real.log (18409 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (18409 / 15625) = -Real.log (15625 / 18409) := by
    rw [show ((18409 / 15625) : ℝ) = ((15625 / 18409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (98114509 / 500000000) ≤ -Real.log (12841 / 15625) ∧
    -Real.log (12841 / 15625) ≤ (196229019 / 1000000000) := by
  have h := checkLog_sound (w := (1392 / 14233)) (n := 12)
    (lo := (98114509 / 500000000)) (hi := (196229019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 12841) = 1/(12841 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-196229019 / 1000000000) (-98114509 / 500000000) (Real.log (12841 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (725994967 / 1000000000) ≤ -Real.log (250000000000 / 516696615753) ∧
    -Real.log (250000000000 / 516696615753) ≤ (725994969 / 1000000000) := by
  have h := checkLog_sound (w := (16696615753 / 1016696615753)) (n := 12)
    (lo := (32847787 / 1000000000)) (hi := (8211947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((516696615753 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(516696615753 / 500000000000) = 1/(250000000000 / 516696615753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (725994967 / 1000000000) (725994969 / 1000000000) (Real.log (516696615753 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (516696615753 / 250000000000) = -Real.log (250000000000 / 516696615753) := by
    rw [show ((516696615753 / 250000000000) : ℝ) = ((250000000000 / 516696615753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (181832117 / 250000000) ≤ -Real.log (100000000000 / 206954436451) ∧
    -Real.log (100000000000 / 206954436451) ≤ (72732847 / 100000000) := by
  have h := checkLog_sound (w := (6954436451 / 406954436451)) (n := 12)
    (lo := (4272661 / 125000000)) (hi := (34181289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((206954436451 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(206954436451 / 200000000000) = 1/(100000000000 / 206954436451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (181832117 / 250000000) (72732847 / 100000000) (Real.log (206954436451 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (206954436451 / 100000000000) = -Real.log (100000000000 / 206954436451) := by
    rw [show ((206954436451 / 100000000000) : ℝ) = ((100000000000 / 206954436451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (101002873 / 200000000) ≤ -Real.log (250000000000 / 414252330861) ∧
    -Real.log (250000000000 / 414252330861) ≤ (252507183 / 500000000) := by
  have h := checkLog_sound (w := (164252330861 / 664252330861)) (n := 12)
    (lo := (101002873 / 200000000)) (hi := (252507183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((414252330861 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(414252330861 / 250000000000) = 1/(250000000000 / 414252330861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (101002873 / 200000000) (252507183 / 500000000) (Real.log (414252330861 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (414252330861 / 250000000000) = -Real.log (250000000000 / 414252330861) := by
    rw [show ((414252330861 / 250000000000) : ℝ) = ((250000000000 / 414252330861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (505913431 / 1000000000) ≤ -Real.log (50000000000 / 82924987771) ∧
    -Real.log (50000000000 / 82924987771) ≤ (63239179 / 125000000) := by
  have h := checkLog_sound (w := (32924987771 / 132924987771)) (n := 12)
    (lo := (505913431 / 1000000000)) (hi := (63239179 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82924987771 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82924987771 / 50000000000) = 1/(50000000000 / 82924987771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (505913431 / 1000000000) (63239179 / 125000000) (Real.log (82924987771 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (82924987771 / 50000000000) = -Real.log (50000000000 / 82924987771) := by
    rw [show ((82924987771 / 50000000000) : ℝ) = ((50000000000 / 82924987771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (71909589 / 200000000) ≤ -Real.log (500000000000 / 716340808963) ∧
    -Real.log (500000000000 / 716340808963) ≤ (179773973 / 500000000) := by
  have h := checkLog_sound (w := (216340808963 / 1216340808963)) (n := 12)
    (lo := (71909589 / 200000000)) (hi := (179773973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((716340808963 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(716340808963 / 500000000000) = 1/(500000000000 / 716340808963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (71909589 / 200000000) (179773973 / 500000000) (Real.log (716340808963 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (716340808963 / 500000000000) = -Real.log (500000000000 / 716340808963) := by
    rw [show ((716340808963 / 500000000000) : ℝ) = ((500000000000 / 716340808963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (180098249 / 500000000) ≤ -Real.log (25000000000 / 35840277237) ∧
    -Real.log (25000000000 / 35840277237) ≤ (360196499 / 1000000000) := by
  have h := checkLog_sound (w := (10840277237 / 60840277237)) (n := 12)
    (lo := (180098249 / 500000000)) (hi := (360196499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35840277237 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35840277237 / 25000000000) = 1/(25000000000 / 35840277237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (180098249 / 500000000) (360196499 / 1000000000) (Real.log (35840277237 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (35840277237 / 25000000000) = -Real.log (25000000000 / 35840277237) := by
    rw [show ((35840277237 / 25000000000) : ℝ) = ((25000000000 / 35840277237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (16130769 / 500000000) ≤ -Real.log (236389969 / 244140625) ∧
    -Real.log (236389969 / 244140625) ≤ (32261539 / 1000000000) := by
  have h := checkLog_sound (w := (3875328 / 240265297)) (n := 12)
    (lo := (16130769 / 500000000)) (hi := (32261539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 236389969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 236389969) = 1/(236389969 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-32261539 / 1000000000) (-16130769 / 500000000) (Real.log (236389969 / 244140625)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8036521 / 250000000) ≤ -Real.log (242091277239 / 250000000000) ∧
    -Real.log (242091277239 / 250000000000) ≤ (6429217 / 200000000) := by
  have h := checkLog_sound (w := (7908722761 / 492091277239)) (n := 12)
    (lo := (8036521 / 250000000)) (hi := (6429217 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242091277239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242091277239) = 1/(242091277239 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-6429217 / 200000000) (-8036521 / 250000000) (Real.log (242091277239 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell167
