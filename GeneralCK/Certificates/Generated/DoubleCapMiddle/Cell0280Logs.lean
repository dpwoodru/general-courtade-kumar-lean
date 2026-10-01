import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0280
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

theorem reflection_log_1_neg : (229063493 / 1000000000) ≤ -Real.log (2560 / 3219) ∧
    -Real.log (2560 / 3219) ≤ (114531747 / 500000000) := by
  have h := checkLog_sound (w := (659 / 5779)) (n := 12)
    (lo := (229063493 / 1000000000)) (hi := (114531747 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3219 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3219 / 2560) = 1/(2560 / 3219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (229063493 / 1000000000) (114531747 / 500000000) (Real.log (3219 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3219 / 2560) = -Real.log (2560 / 3219) := by
    rw [show ((3219 / 2560) : ℝ) = ((2560 / 3219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (148813597 / 500000000) ≤ -Real.log (1901 / 2560) ∧
    -Real.log (1901 / 2560) ≤ (59525439 / 200000000) := by
  have h := checkLog_sound (w := (659 / 4461)) (n := 12)
    (lo := (148813597 / 500000000)) (hi := (59525439 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1901) = 1/(1901 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-59525439 / 200000000) (-148813597 / 500000000) (Real.log (1901 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (228597401 / 1000000000) ≤ -Real.log (1024 / 1287) ∧
    -Real.log (1024 / 1287) ≤ (114298701 / 500000000) := by
  have h := checkLog_sound (w := (263 / 2311)) (n := 12)
    (lo := (228597401 / 1000000000)) (hi := (114298701 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1287 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1287 / 1024) = 1/(1024 / 1287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (228597401 / 1000000000) (114298701 / 500000000) (Real.log (1287 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1287 / 1024) = -Real.log (1024 / 1287) := by
    rw [show ((1287 / 1024) : ℝ) = ((1024 / 1287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (296838447 / 1000000000) ≤ -Real.log (761 / 1024) ∧
    -Real.log (761 / 1024) ≤ (18552403 / 62500000) := by
  have h := checkLog_sound (w := (263 / 1785)) (n := 12)
    (lo := (296838447 / 1000000000)) (hi := (18552403 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 761) = 1/(761 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-18552403 / 62500000) (-296838447 / 1000000000) (Real.log (761 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (207656149 / 500000000) ≤ -Real.log (1280 / 1939) ∧
    -Real.log (1280 / 1939) ≤ (415312299 / 1000000000) := by
  have h := checkLog_sound (w := (659 / 3219)) (n := 12)
    (lo := (207656149 / 500000000)) (hi := (415312299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1939 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1939 / 1280) = 1/(1280 / 1939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (207656149 / 500000000) (415312299 / 1000000000) (Real.log (1939 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1939 / 1280) = -Real.log (1280 / 1939) := by
    rw [show ((1939 / 1280) : ℝ) = ((1280 / 1939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (361642137 / 500000000) ≤ -Real.log (621 / 1280) ∧
    -Real.log (621 / 1280) ≤ (180821069 / 250000000) := by
  have h := checkLog_sound (w := (19 / 1261)) (n := 12)
    (lo := (15068547 / 500000000)) (hi := (6027419 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 621) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 621) = 1/(621 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-180821069 / 250000000) (-361642137 / 500000000) (Real.log (621 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (103634601 / 250000000) ≤ -Real.log (512 / 775) ∧
    -Real.log (512 / 775) ≤ (82907681 / 200000000) := by
  have h := checkLog_sound (w := (263 / 1287)) (n := 12)
    (lo := (103634601 / 250000000)) (hi := (82907681 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((775 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(775 / 512) = 1/(512 / 775) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (103634601 / 250000000) (82907681 / 200000000) (Real.log (775 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (775 / 512) = -Real.log (512 / 775) := by
    rw [show ((775 / 512) : ℝ) = ((512 / 775) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (45054483 / 62500000) ≤ -Real.log (249 / 512) ∧
    -Real.log (249 / 512) ≤ (72087173 / 100000000) := by
  have h := checkLog_sound (w := (7 / 505)) (n := 12)
    (lo := (6931137 / 250000000)) (hi := (27724549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 249) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 249) = 1/(249 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-72087173 / 100000000) (-45054483 / 62500000) (Real.log (249 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (12525951 / 40000000) ≤ -Real.log (40000 / 54709) ∧
    -Real.log (40000 / 54709) ≤ (39143597 / 125000000) := by
  have h := checkLog_sound (w := (14709 / 94709)) (n := 12)
    (lo := (12525951 / 40000000)) (hi := (39143597 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54709 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54709 / 40000) = 1/(40000 / 54709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (12525951 / 40000000) (39143597 / 125000000) (Real.log (54709 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (54709 / 40000) = -Real.log (40000 / 54709) := by
    rw [show ((54709 / 40000) : ℝ) = ((40000 / 54709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (114607713 / 250000000) ≤ -Real.log (25291 / 40000) ∧
    -Real.log (25291 / 40000) ≤ (458430853 / 1000000000) := by
  have h := checkLog_sound (w := (14709 / 65291)) (n := 12)
    (lo := (114607713 / 250000000)) (hi := (458430853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 25291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 25291) = 1/(25291 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-458430853 / 1000000000) (-114607713 / 250000000) (Real.log (25291 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (313779551 / 1000000000) ≤ -Real.log (250000 / 342147) ∧
    -Real.log (250000 / 342147) ≤ (9805611 / 31250000) := by
  have h := checkLog_sound (w := (92147 / 592147)) (n := 12)
    (lo := (313779551 / 1000000000)) (hi := (9805611 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342147 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342147 / 250000) = 1/(250000 / 342147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (313779551 / 1000000000) (9805611 / 31250000) (Real.log (342147 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (342147 / 250000) = -Real.log (250000 / 342147) := by
    rw [show ((342147 / 250000) : ℝ) = ((250000 / 342147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (459796697 / 1000000000) ≤ -Real.log (157853 / 250000) ∧
    -Real.log (157853 / 250000) ≤ (229898349 / 500000000) := by
  have h := checkLog_sound (w := (92147 / 407853)) (n := 12)
    (lo := (459796697 / 1000000000)) (hi := (229898349 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 157853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 157853) = 1/(157853 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-229898349 / 500000000) (-459796697 / 1000000000) (Real.log (157853 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (5977883 / 25000000) ≤ -Real.log (8000 / 10161) ∧
    -Real.log (8000 / 10161) ≤ (239115321 / 1000000000) := by
  have h := checkLog_sound (w := (2161 / 18161)) (n := 12)
    (lo := (5977883 / 25000000)) (hi := (239115321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10161 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10161 / 8000) = 1/(8000 / 10161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (5977883 / 25000000) (239115321 / 1000000000) (Real.log (10161 / 8000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (10161 / 8000) = -Real.log (8000 / 10161) := by
    rw [show ((10161 / 8000) : ℝ) = ((8000 / 10161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (39360249 / 125000000) ≤ -Real.log (5839 / 8000) ∧
    -Real.log (5839 / 8000) ≤ (314881993 / 1000000000) := by
  have h := checkLog_sound (w := (2161 / 13839)) (n := 12)
    (lo := (39360249 / 125000000)) (hi := (314881993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 5839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 5839) = 1/(5839 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-314881993 / 1000000000) (-39360249 / 125000000) (Real.log (5839 / 8000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (119826459 / 500000000) ≤ -Real.log (125000 / 158851) ∧
    -Real.log (125000 / 158851) ≤ (239652919 / 1000000000) := by
  have h := checkLog_sound (w := (33851 / 283851)) (n := 12)
    (lo := (119826459 / 500000000)) (hi := (239652919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158851 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(158851 / 125000) = 1/(125000 / 158851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (119826459 / 500000000) (239652919 / 1000000000) (Real.log (158851 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (158851 / 125000) = -Real.log (125000 / 158851) := by
    rw [show ((158851 / 125000) : ℝ) = ((125000 / 158851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (315818207 / 1000000000) ≤ -Real.log (91149 / 125000) ∧
    -Real.log (91149 / 125000) ≤ (9869319 / 31250000) := by
  have h := checkLog_sound (w := (33851 / 216149)) (n := 12)
    (lo := (315818207 / 1000000000)) (hi := (9869319 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 91149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 91149) = 1/(91149 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-9869319 / 31250000) (-315818207 / 1000000000) (Real.log (91149 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (771579627 / 1000000000) ≤ -Real.log (100000000000 / 216318057807) ∧
    -Real.log (100000000000 / 216318057807) ≤ (771579629 / 1000000000) := by
  have h := checkLog_sound (w := (16318057807 / 416318057807)) (n := 12)
    (lo := (78432447 / 1000000000)) (hi := (1225507 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216318057807 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(216318057807 / 200000000000) = 1/(100000000000 / 216318057807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (771579627 / 1000000000) (771579629 / 1000000000) (Real.log (216318057807 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (216318057807 / 100000000000) = -Real.log (100000000000 / 216318057807) := by
    rw [show ((216318057807 / 100000000000) : ℝ) = ((100000000000 / 216318057807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (96697031 / 125000000) ≤ -Real.log (125000000000 / 270937992943) ∧
    -Real.log (125000000000 / 270937992943) ≤ (618861 / 800000) := by
  have h := checkLog_sound (w := (20937992943 / 520937992943)) (n := 12)
    (lo := (20107267 / 250000000)) (hi := (80429069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270937992943 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(270937992943 / 250000000000) = 1/(125000000000 / 270937992943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (96697031 / 125000000) (618861 / 800000) (Real.log (270937992943 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (270937992943 / 125000000000) = -Real.log (125000000000 / 270937992943) := by
    rw [show ((270937992943 / 125000000000) : ℝ) = ((125000000000 / 270937992943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (553997313 / 1000000000) ≤ -Real.log (100000000000 / 174019523891) ∧
    -Real.log (100000000000 / 174019523891) ≤ (276998657 / 500000000) := by
  have h := checkLog_sound (w := (74019523891 / 274019523891)) (n := 12)
    (lo := (553997313 / 1000000000)) (hi := (276998657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((174019523891 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(174019523891 / 100000000000) = 1/(100000000000 / 174019523891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (553997313 / 1000000000) (276998657 / 500000000) (Real.log (174019523891 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (174019523891 / 100000000000) = -Real.log (100000000000 / 174019523891) := by
    rw [show ((174019523891 / 100000000000) : ℝ) = ((100000000000 / 174019523891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4443769 / 8000000) ≤ -Real.log (500000000000 / 871380925737) ∧
    -Real.log (500000000000 / 871380925737) ≤ (277735563 / 500000000) := by
  have h := checkLog_sound (w := (371380925737 / 1371380925737)) (n := 12)
    (lo := (4443769 / 8000000)) (hi := (277735563 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((871380925737 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(871380925737 / 500000000000) = 1/(500000000000 / 871380925737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4443769 / 8000000) (277735563 / 500000000) (Real.log (871380925737 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (871380925737 / 500000000000) = -Real.log (500000000000 / 871380925737) := by
    rw [show ((871380925737 / 500000000000) : ℝ) = ((500000000000 / 871380925737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0280
