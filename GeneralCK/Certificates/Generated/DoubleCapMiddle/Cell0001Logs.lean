import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0001
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

theorem reflection_log_1_neg : (462160451 / 1000000000) ≤ -Real.log (80 / 127) ∧
    -Real.log (80 / 127) ≤ (115540113 / 250000000) := by
  have h := checkLog_sound (w := (47 / 207)) (n := 12)
    (lo := (462160451 / 1000000000)) (hi := (115540113 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(127 / 80) = 1/(80 / 127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (462160451 / 1000000000) (115540113 / 250000000) (Real.log (127 / 80)) := by
  have h := reflection_log_1_neg
  have he : Real.log (127 / 80) = -Real.log (80 / 127) := by
    rw [show ((127 / 80) : ℝ) = ((80 / 127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (27672471 / 31250000) ≤ -Real.log (33 / 80) ∧
    -Real.log (33 / 80) ≤ (442759537 / 500000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 33) = 1/(33 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-442759537 / 500000000) (-27672471 / 31250000) (Real.log (33 / 80)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (56781909 / 125000000) ≤ -Real.log (40 / 63) ∧
    -Real.log (40 / 63) ≤ (454255273 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 103)) (n := 12)
    (lo := (56781909 / 125000000)) (hi := (454255273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63 / 40) = 1/(40 / 63) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (56781909 / 125000000) (454255273 / 1000000000) (Real.log (63 / 40)) := by
  have h := reflection_log_3_neg
  have he : Real.log (63 / 40) = -Real.log (40 / 63) := by
    rw [show ((63 / 40) : ℝ) = ((40 / 63) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (855666109 / 1000000000) ≤ -Real.log (17 / 40) ∧
    -Real.log (17 / 40) ≤ (855666111 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 37)) (n := 12)
    (lo := (162518929 / 1000000000)) (hi := (16251893 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 17) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20 / 17) = 1/(17 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-855666111 / 1000000000) (-855666109 / 1000000000) (Real.log (17 / 40)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (161268147 / 1000000000) ≤ -Real.log (40 / 47) ∧
    -Real.log (40 / 47) ≤ (40317037 / 250000000) := by
  have h := checkLog_sound (w := (7 / 87)) (n := 12)
    (lo := (161268147 / 1000000000)) (hi := (40317037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47 / 40) = 1/(40 / 47) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (161268147 / 1000000000) (40317037 / 250000000) (Real.log (47 / 40)) := by
  have h := reflection_log_5_neg
  have he : Real.log (47 / 40) = -Real.log (40 / 47) := by
    rw [show ((47 / 40) : ℝ) = ((40 / 47) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (48092973 / 250000000) ≤ -Real.log (33 / 40) ∧
    -Real.log (33 / 40) ≤ (192371893 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 33) = 1/(33 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-192371893 / 1000000000) (-48092973 / 250000000) (Real.log (33 / 40)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (69880971 / 500000000) ≤ -Real.log (20 / 23) ∧
    -Real.log (20 / 23) ≤ (139761943 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 43)) (n := 12)
    (lo := (69880971 / 500000000)) (hi := (139761943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23 / 20) = 1/(20 / 23) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (69880971 / 500000000) (139761943 / 1000000000) (Real.log (23 / 20)) := by
  have h := reflection_log_7_neg
  have he : Real.log (23 / 20) = -Real.log (20 / 23) := by
    rw [show ((23 / 20) : ℝ) = ((20 / 23) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (162518929 / 1000000000) ≤ -Real.log (17 / 20) ∧
    -Real.log (17 / 20) ≤ (16251893 / 100000000) := by
  have h := checkLog_sound (w := (3 / 37)) (n := 12)
    (lo := (162518929 / 1000000000)) (hi := (16251893 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 17) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20 / 17) = 1/(17 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-16251893 / 100000000) (-162518929 / 1000000000) (Real.log (17 / 20)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (579592069 / 1000000000) ≤ -Real.log (100000 / 178531) ∧
    -Real.log (100000 / 178531) ≤ (57959207 / 100000000) := by
  have h := checkLog_sound (w := (78531 / 278531)) (n := 12)
    (lo := (579592069 / 1000000000)) (hi := (57959207 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178531 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178531 / 100000) = 1/(100000 / 178531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (579592069 / 1000000000) (57959207 / 100000000) (Real.log (178531 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (178531 / 100000) = -Real.log (100000 / 178531) := by
    rw [show ((178531 / 100000) : ℝ) = ((100000 / 178531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (30771203 / 20000000) ≤ -Real.log (21469 / 100000) ∧
    -Real.log (21469 / 100000) ≤ (1538560153 / 1000000000) := by
  have h := checkLog_sound (w := (3531 / 46469)) (n := 12)
    (lo := (15226579 / 100000000)) (hi := (152265791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 21469) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(25000 / 21469) = 1/(21469 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1538560153 / 1000000000) (-30771203 / 20000000) (Real.log (21469 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (580673649 / 1000000000) ≤ -Real.log (500000 / 893621) ∧
    -Real.log (500000 / 893621) ≤ (11613473 / 20000000) := by
  have h := checkLog_sound (w := (393621 / 1393621)) (n := 12)
    (lo := (580673649 / 1000000000)) (hi := (11613473 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((893621 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(893621 / 500000) = 1/(500000 / 893621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (580673649 / 1000000000) (11613473 / 20000000) (Real.log (893621 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (893621 / 500000) = -Real.log (500000 / 893621) := by
    rw [show ((893621 / 500000) : ℝ) = ((500000 / 893621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (386899977 / 250000000) ≤ -Real.log (106379 / 500000) ∧
    -Real.log (106379 / 500000) ≤ (1547599911 / 1000000000) := by
  have h := checkLog_sound (w := (18621 / 231379)) (n := 12)
    (lo := (40326387 / 250000000)) (hi := (161305549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 106379) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 106379) = 1/(106379 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1547599911 / 1000000000) (-386899977 / 250000000) (Real.log (106379 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (533701171 / 1000000000) ≤ -Real.log (62500 / 106577) ∧
    -Real.log (62500 / 106577) ≤ (133425293 / 250000000) := by
  have h := checkLog_sound (w := (44077 / 169077)) (n := 12)
    (lo := (533701171 / 1000000000)) (hi := (133425293 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((106577 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(106577 / 62500) = 1/(62500 / 106577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (533701171 / 1000000000) (133425293 / 250000000) (Real.log (106577 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (106577 / 62500) = -Real.log (62500 / 106577) := by
    rw [show ((106577 / 62500) : ℝ) = ((62500 / 106577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (76347917 / 62500000) ≤ -Real.log (18423 / 62500) ∧
    -Real.log (18423 / 62500) ≤ (610783337 / 500000000) := by
  have h := checkLog_sound (w := (12827 / 49673)) (n := 12)
    (lo := (132104873 / 250000000)) (hi := (528419493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18423) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 18423) = 1/(18423 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-610783337 / 500000000) (-76347917 / 62500000) (Real.log (18423 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (538246219 / 1000000000) ≤ -Real.log (1000 / 1713) ∧
    -Real.log (1000 / 1713) ≤ (26912311 / 50000000) := by
  have h := checkLog_sound (w := (713 / 2713)) (n := 12)
    (lo := (538246219 / 1000000000)) (hi := (26912311 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1713 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1713 / 1000) = 1/(1000 / 1713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (538246219 / 1000000000) (26912311 / 50000000) (Real.log (1713 / 1000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1713 / 1000) = -Real.log (1000 / 1713) := by
    rw [show ((1713 / 1000) : ℝ) = ((1000 / 1713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (624136531 / 500000000) ≤ -Real.log (287 / 1000) ∧
    -Real.log (287 / 1000) ≤ (156034133 / 125000000) := by
  have h := checkLog_sound (w := (213 / 787)) (n := 12)
    (lo := (277562941 / 500000000)) (hi := (555125883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 287) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 287) = 1/(287 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-156034133 / 125000000) (-624136531 / 500000000) (Real.log (287 / 1000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2118152219 / 1000000000) ≤ -Real.log (500000000000 / 4157878801993) ∧
    -Real.log (500000000000 / 4157878801993) ≤ (2118152223 / 1000000000) := by
  have h := checkLog_sound (w := (157878801993 / 8157878801993)) (n := 12)
    (lo := (38710679 / 1000000000)) (hi := (967767 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4157878801993 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4157878801993 / 4000000000000) = 1/(500000000000 / 4157878801993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2118152219 / 1000000000) (2118152223 / 1000000000) (Real.log (4157878801993 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4157878801993 / 500000000000) = -Real.log (500000000000 / 4157878801993) := by
    rw [show ((4157878801993 / 500000000000) : ℝ) = ((500000000000 / 4157878801993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2128273557 / 1000000000) ≤ -Real.log (20000000000 / 168007031463) ∧
    -Real.log (20000000000 / 168007031463) ≤ (2128273561 / 1000000000) := by
  have h := checkLog_sound (w := (8007031463 / 328007031463)) (n := 12)
    (lo := (48832017 / 1000000000)) (hi := (24416009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168007031463 / 160000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(168007031463 / 160000000000) = 1/(20000000000 / 168007031463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2128273557 / 1000000000) (2128273561 / 1000000000) (Real.log (168007031463 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (168007031463 / 20000000000) = -Real.log (20000000000 / 168007031463) := by
    rw [show ((168007031463 / 20000000000) : ℝ) = ((20000000000 / 168007031463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1755267843 / 1000000000) ≤ -Real.log (5000000000 / 28924985073) ∧
    -Real.log (5000000000 / 28924985073) ≤ (877633923 / 500000000) := by
  have h := checkLog_sound (w := (8924985073 / 48924985073)) (n := 12)
    (lo := (368973483 / 1000000000)) (hi := (92243371 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28924985073 / 20000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(28924985073 / 20000000000) = 1/(5000000000 / 28924985073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1755267843 / 1000000000) (877633923 / 500000000) (Real.log (28924985073 / 5000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (28924985073 / 5000000000) = -Real.log (5000000000 / 28924985073) := by
    rw [show ((28924985073 / 5000000000) : ℝ) = ((5000000000 / 28924985073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1786519281 / 1000000000) ≤ -Real.log (125000000000 / 746080139373) ∧
    -Real.log (125000000000 / 746080139373) ≤ (446629821 / 250000000) := by
  have h := checkLog_sound (w := (246080139373 / 1246080139373)) (n := 12)
    (lo := (400224921 / 1000000000)) (hi := (200112461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746080139373 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(746080139373 / 500000000000) = 1/(125000000000 / 746080139373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1786519281 / 1000000000) (446629821 / 250000000) (Real.log (746080139373 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (746080139373 / 125000000000) = -Real.log (125000000000 / 746080139373) := by
    rw [show ((746080139373 / 125000000000) : ℝ) = ((125000000000 / 746080139373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0001
