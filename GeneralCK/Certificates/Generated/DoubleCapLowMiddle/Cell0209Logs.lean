import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0209
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

theorem reflection_log_1_neg : (140528167 / 250000000) ≤ -Real.log (1600 / 2807) ∧
    -Real.log (1600 / 2807) ≤ (562112669 / 1000000000) := by
  have h := checkLog_sound (w := (1207 / 4407)) (n := 12)
    (lo := (140528167 / 250000000)) (hi := (562112669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2807 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2807 / 1600) = 1/(1600 / 2807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (140528167 / 250000000) (562112669 / 1000000000) (Real.log (2807 / 1600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2807 / 1600) = -Real.log (1600 / 2807) := by
    rw [show ((2807 / 1600) : ℝ) = ((1600 / 2807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (280789859 / 200000000) ≤ -Real.log (393 / 1600) ∧
    -Real.log (393 / 1600) ≤ (701974649 / 500000000) := by
  have h := checkLog_sound (w := (7 / 793)) (n := 12)
    (lo := (3530987 / 200000000)) (hi := (2206867 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 393) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 393) = 1/(393 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-701974649 / 500000000) (-280789859 / 200000000) (Real.log (393 / 1600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (558722531 / 1000000000) ≤ -Real.log (640 / 1119) ∧
    -Real.log (640 / 1119) ≤ (139680633 / 250000000) := by
  have h := checkLog_sound (w := (479 / 1759)) (n := 12)
    (lo := (558722531 / 1000000000)) (hi := (139680633 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1119 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1119 / 640) = 1/(640 / 1119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (558722531 / 1000000000) (139680633 / 250000000) (Real.log (1119 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1119 / 640) = -Real.log (640 / 1119) := by
    rw [show ((1119 / 640) : ℝ) = ((640 / 1119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (138006381 / 100000000) ≤ -Real.log (161 / 640) ∧
    -Real.log (161 / 640) ≤ (345015953 / 250000000) := by
  have h := checkLog_sound (w := (159 / 481)) (n := 12)
    (lo := (68691663 / 100000000)) (hi := (686916631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 161) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320 / 161) = 1/(161 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-345015953 / 250000000) (-138006381 / 100000000) (Real.log (161 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (411281493 / 1000000000) ≤ -Real.log (800 / 1207) ∧
    -Real.log (800 / 1207) ≤ (205640747 / 500000000) := by
  have h := checkLog_sound (w := (407 / 2007)) (n := 12)
    (lo := (411281493 / 1000000000)) (hi := (205640747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1207 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1207 / 800) = 1/(800 / 1207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (411281493 / 1000000000) (205640747 / 500000000) (Real.log (1207 / 800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1207 / 800) = -Real.log (800 / 1207) := by
    rw [show ((1207 / 800) : ℝ) = ((800 / 1207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (142160423 / 200000000) ≤ -Real.log (393 / 800) ∧
    -Real.log (393 / 800) ≤ (710802117 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 793)) (n := 12)
    (lo := (3530987 / 200000000)) (hi := (2206867 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 393) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(400 / 393) = 1/(393 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-710802117 / 1000000000) (-142160423 / 200000000) (Real.log (393 / 800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (403379601 / 1000000000) ≤ -Real.log (320 / 479) ∧
    -Real.log (320 / 479) ≤ (201689801 / 500000000) := by
  have h := checkLog_sound (w := (159 / 799)) (n := 12)
    (lo := (403379601 / 1000000000)) (hi := (201689801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((479 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(479 / 320) = 1/(320 / 479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (403379601 / 1000000000) (201689801 / 500000000) (Real.log (479 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (479 / 320) = -Real.log (320 / 479) := by
    rw [show ((479 / 320) : ℝ) = ((320 / 479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (68691663 / 100000000) ≤ -Real.log (161 / 320) ∧
    -Real.log (161 / 320) ≤ (686916631 / 1000000000) := by
  have h := checkLog_sound (w := (159 / 481)) (n := 12)
    (lo := (68691663 / 100000000)) (hi := (686916631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(320 / 161) = 1/(161 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-686916631 / 1000000000) (-68691663 / 100000000) (Real.log (161 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (608311253 / 1000000000) ≤ -Real.log (500000 / 918663) ∧
    -Real.log (500000 / 918663) ≤ (304155627 / 500000000) := by
  have h := checkLog_sound (w := (418663 / 1418663)) (n := 12)
    (lo := (608311253 / 1000000000)) (hi := (304155627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((918663 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(918663 / 500000) = 1/(500000 / 918663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (608311253 / 1000000000) (304155627 / 500000000) (Real.log (918663 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (918663 / 500000) = -Real.log (500000 / 918663) := by
    rw [show ((918663 / 500000) : ℝ) = ((500000 / 918663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1816007079 / 1000000000) ≤ -Real.log (81337 / 500000) ∧
    -Real.log (81337 / 500000) ≤ (908003541 / 500000000) := by
  have h := checkLog_sound (w := (43663 / 206337)) (n := 12)
    (lo := (429712719 / 1000000000)) (hi := (5371409 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 81337) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 81337) = 1/(81337 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-908003541 / 500000000) (-1816007079 / 1000000000) (Real.log (81337 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (609779701 / 1000000000) ≤ -Real.log (500000 / 920013) ∧
    -Real.log (500000 / 920013) ≤ (304889851 / 500000000) := by
  have h := checkLog_sound (w := (420013 / 1420013)) (n := 12)
    (lo := (609779701 / 1000000000)) (hi := (304889851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((920013 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(920013 / 500000) = 1/(500000 / 920013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (609779701 / 1000000000) (304889851 / 500000000) (Real.log (920013 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (920013 / 500000) = -Real.log (500000 / 920013) := by
    rw [show ((920013 / 500000) : ℝ) = ((500000 / 920013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (73309759 / 40000000) ≤ -Real.log (79987 / 500000) ∧
    -Real.log (79987 / 500000) ≤ (916371989 / 500000000) := by
  have h := checkLog_sound (w := (45013 / 204987)) (n := 12)
    (lo := (89289923 / 200000000)) (hi := (27903101 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 79987) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 79987) = 1/(79987 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-916371989 / 500000000) (-73309759 / 40000000) (Real.log (79987 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (149128231 / 250000000) ≤ -Real.log (31250 / 56743) ∧
    -Real.log (31250 / 56743) ≤ (23860517 / 40000000) := by
  have h := checkLog_sound (w := (25493 / 87993)) (n := 12)
    (lo := (149128231 / 250000000)) (hi := (23860517 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56743 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(56743 / 31250) = 1/(31250 / 56743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (149128231 / 250000000) (23860517 / 40000000) (Real.log (56743 / 31250)) := by
  have h := reflection_log_13_neg
  have he : Real.log (56743 / 31250) = -Real.log (31250 / 56743) := by
    rw [show ((56743 / 31250) : ℝ) = ((31250 / 56743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1691602869 / 1000000000) ≤ -Real.log (5757 / 31250) ∧
    -Real.log (5757 / 31250) ≤ (211450359 / 125000000) := by
  have h := checkLog_sound (w := (4111 / 27139)) (n := 12)
    (lo := (305308509 / 1000000000)) (hi := (30530851 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 11514) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(15625 / 11514) = 1/(5757 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-211450359 / 125000000) (-1691602869 / 1000000000) (Real.log (5757 / 31250)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (598674949 / 1000000000) ≤ -Real.log (500000 / 909853) ∧
    -Real.log (500000 / 909853) ≤ (11973499 / 20000000) := by
  have h := checkLog_sound (w := (409853 / 1409853)) (n := 12)
    (lo := (598674949 / 1000000000)) (hi := (11973499 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((909853 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(909853 / 500000) = 1/(500000 / 909853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (598674949 / 1000000000) (11973499 / 20000000) (Real.log (909853 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (909853 / 500000) = -Real.log (500000 / 909853) := by
    rw [show ((909853 / 500000) : ℝ) = ((500000 / 909853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (856583213 / 500000000) ≤ -Real.log (90147 / 500000) ∧
    -Real.log (90147 / 500000) ≤ (1713166429 / 1000000000) := by
  have h := checkLog_sound (w := (34853 / 215147)) (n := 12)
    (lo := (163436033 / 500000000)) (hi := (326872067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 90147) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 90147) = 1/(90147 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1713166429 / 1000000000) (-856583213 / 500000000) (Real.log (90147 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (606079583 / 250000000) ≤ -Real.log (500000000000 / 5647263852859) ∧
    -Real.log (500000000000 / 5647263852859) ≤ (18939987 / 7812500) := by
  have h := checkLog_sound (w := (1647263852859 / 9647263852859)) (n := 12)
    (lo := (43109599 / 125000000)) (hi := (344876793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5647263852859 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5647263852859 / 4000000000000) = 1/(500000000000 / 5647263852859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (606079583 / 250000000) (18939987 / 7812500) (Real.log (5647263852859 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5647263852859 / 500000000000) = -Real.log (500000000000 / 5647263852859) := by
    rw [show ((5647263852859 / 500000000000) : ℝ) = ((500000000000 / 5647263852859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2442523677 / 1000000000) ≤ -Real.log (250000000000 / 2875507895033) ∧
    -Real.log (250000000000 / 2875507895033) ≤ (2442523681 / 1000000000) := by
  have h := checkLog_sound (w := (875507895033 / 4875507895033)) (n := 12)
    (lo := (363082137 / 1000000000)) (hi := (181541069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2875507895033 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2875507895033 / 2000000000000) = 1/(250000000000 / 2875507895033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2442523677 / 1000000000) (2442523681 / 1000000000) (Real.log (2875507895033 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2875507895033 / 250000000000) = -Real.log (250000000000 / 2875507895033) := by
    rw [show ((2875507895033 / 250000000000) : ℝ) = ((250000000000 / 2875507895033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2288115793 / 1000000000) ≤ -Real.log (500000000000 / 4928174396387) ∧
    -Real.log (500000000000 / 4928174396387) ≤ (2288115797 / 1000000000) := by
  have h := checkLog_sound (w := (928174396387 / 8928174396387)) (n := 12)
    (lo := (208674253 / 1000000000)) (hi := (104337127 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4928174396387 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4928174396387 / 4000000000000) = 1/(500000000000 / 4928174396387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2288115793 / 1000000000) (2288115797 / 1000000000) (Real.log (4928174396387 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4928174396387 / 500000000000) = -Real.log (500000000000 / 4928174396387) := by
    rw [show ((4928174396387 / 500000000000) : ℝ) = ((500000000000 / 4928174396387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (18494731 / 8000000) ≤ -Real.log (500000000000 / 5046496278301) ∧
    -Real.log (500000000000 / 5046496278301) ≤ (2311841379 / 1000000000) := by
  have h := checkLog_sound (w := (1046496278301 / 9046496278301)) (n := 12)
    (lo := (46479967 / 200000000)) (hi := (58099959 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5046496278301 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5046496278301 / 4000000000000) = 1/(500000000000 / 5046496278301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (18494731 / 8000000) (2311841379 / 1000000000) (Real.log (5046496278301 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (5046496278301 / 500000000000) = -Real.log (500000000000 / 5046496278301) := by
    rw [show ((5046496278301 / 500000000000) : ℝ) = ((500000000000 / 5046496278301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0209
