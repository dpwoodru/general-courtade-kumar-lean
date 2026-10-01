import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0039
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

theorem reflection_log_1_neg : (191673651 / 500000000) ≤ -Real.log (640 / 939) ∧
    -Real.log (640 / 939) ≤ (383347303 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 1579)) (n := 12)
    (lo := (191673651 / 500000000)) (hi := (383347303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((939 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(939 / 640) = 1/(640 / 939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (191673651 / 500000000) (383347303 / 1000000000) (Real.log (939 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (939 / 640) = -Real.log (640 / 939) := by
    rw [show ((939 / 640) : ℝ) = ((640 / 939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (629585699 / 1000000000) ≤ -Real.log (341 / 640) ∧
    -Real.log (341 / 640) ≤ (6295857 / 10000000) := by
  have h := checkLog_sound (w := (299 / 981)) (n := 12)
    (lo := (629585699 / 1000000000)) (hi := (6295857 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 341) = 1/(341 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-6295857 / 10000000) (-629585699 / 1000000000) (Real.log (341 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (382548261 / 1000000000) ≤ -Real.log (2560 / 3753) ∧
    -Real.log (2560 / 3753) ≤ (191274131 / 500000000) := by
  have h := checkLog_sound (w := (1193 / 6313)) (n := 12)
    (lo := (382548261 / 1000000000)) (hi := (191274131 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3753 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3753 / 2560) = 1/(2560 / 3753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (382548261 / 1000000000) (191274131 / 500000000) (Real.log (3753 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3753 / 2560) = -Real.log (2560 / 3753) := by
    rw [show ((3753 / 2560) : ℝ) = ((2560 / 3753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (6273887 / 10000000) ≤ -Real.log (1367 / 2560) ∧
    -Real.log (1367 / 2560) ≤ (627388701 / 1000000000) := by
  have h := checkLog_sound (w := (1193 / 3927)) (n := 12)
    (lo := (6273887 / 10000000)) (hi := (627388701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1367) = 1/(1367 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-627388701 / 1000000000) (-6273887 / 10000000) (Real.log (1367 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (164946069 / 250000000) ≤ -Real.log (320 / 619) ∧
    -Real.log (320 / 619) ≤ (659784277 / 1000000000) := by
  have h := checkLog_sound (w := (299 / 939)) (n := 12)
    (lo := (164946069 / 250000000)) (hi := (659784277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((619 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(619 / 320) = 1/(320 / 619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (164946069 / 250000000) (659784277 / 1000000000) (Real.log (619 / 320)) := by
  have h := reflection_log_5_neg
  have he : Real.log (619 / 320) = -Real.log (320 / 619) := by
    rw [show ((619 / 320) : ℝ) = ((320 / 619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (680949639 / 250000000) ≤ -Real.log (21 / 320) ∧
    -Real.log (21 / 320) ≤ (17023741 / 6250000) := by
  have h := checkLog_sound (w := (19 / 61)) (n := 12)
    (lo := (80544627 / 125000000)) (hi := (644357017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 21) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(40 / 21) = 1/(21 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-17023741 / 6250000) (-680949639 / 250000000) (Real.log (21 / 320)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (65857191 / 100000000) ≤ -Real.log (1280 / 2473) ∧
    -Real.log (1280 / 2473) ≤ (658571911 / 1000000000) := by
  have h := checkLog_sound (w := (1193 / 3753)) (n := 12)
    (lo := (65857191 / 100000000)) (hi := (658571911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2473 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2473 / 1280) = 1/(1280 / 2473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (65857191 / 100000000) (658571911 / 1000000000) (Real.log (2473 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2473 / 1280) = -Real.log (1280 / 2473) := by
    rw [show ((2473 / 1280) : ℝ) = ((1280 / 2473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (672176809 / 250000000) ≤ -Real.log (87 / 1280) ∧
    -Real.log (87 / 1280) ≤ (67217681 / 25000000) := by
  have h := checkLog_sound (w := (73 / 247)) (n := 12)
    (lo := (19039553 / 31250000)) (hi := (609265697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 87) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 87) = 1/(87 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-67217681 / 25000000) (-672176809 / 250000000) (Real.log (87 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (531959717 / 1000000000) ≤ -Real.log (200000 / 340453) ∧
    -Real.log (200000 / 340453) ≤ (265979859 / 500000000) := by
  have h := checkLog_sound (w := (140453 / 540453)) (n := 12)
    (lo := (531959717 / 1000000000)) (hi := (265979859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340453 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340453 / 200000) = 1/(200000 / 340453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (531959717 / 1000000000) (265979859 / 500000000) (Real.log (340453 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (340453 / 200000) = -Real.log (200000 / 340453) := by
    rw [show ((340453 / 200000) : ℝ) = ((200000 / 340453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1211551449 / 1000000000) ≤ -Real.log (59547 / 200000) ∧
    -Real.log (59547 / 200000) ≤ (1211551451 / 1000000000) := by
  have h := checkLog_sound (w := (40453 / 159547)) (n := 12)
    (lo := (518404269 / 1000000000)) (hi := (51840427 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 59547) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 59547) = 1/(59547 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1211551451 / 1000000000) (-1211551449 / 1000000000) (Real.log (59547 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (266642653 / 500000000) ≤ -Real.log (1000000 / 1704523) ∧
    -Real.log (1000000 / 1704523) ≤ (533285307 / 1000000000) := by
  have h := checkLog_sound (w := (704523 / 2704523)) (n := 12)
    (lo := (266642653 / 500000000)) (hi := (533285307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1704523 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1704523 / 1000000) = 1/(1000000 / 1704523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (266642653 / 500000000) (533285307 / 1000000000) (Real.log (1704523 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1704523 / 1000000) = -Real.log (1000000 / 1704523) := by
    rw [show ((1704523 / 1000000) : ℝ) = ((1000000 / 1704523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (609582139 / 500000000) ≤ -Real.log (295477 / 1000000) ∧
    -Real.log (295477 / 1000000) ≤ (30479107 / 25000000) := by
  have h := checkLog_sound (w := (204523 / 795477)) (n := 12)
    (lo := (263008549 / 500000000)) (hi := (526017099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 295477) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 295477) = 1/(295477 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-30479107 / 25000000) (-609582139 / 500000000) (Real.log (295477 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (453486087 / 1000000000) ≤ -Real.log (1000000 / 1573789) ∧
    -Real.log (1000000 / 1573789) ≤ (56685761 / 125000000) := by
  have h := checkLog_sound (w := (573789 / 2573789)) (n := 12)
    (lo := (453486087 / 1000000000)) (hi := (56685761 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1573789 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1573789 / 1000000) = 1/(1000000 / 1573789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (453486087 / 1000000000) (56685761 / 125000000) (Real.log (1573789 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1573789 / 1000000) = -Real.log (1000000 / 1573789) := by
    rw [show ((1573789 / 1000000) : ℝ) = ((1000000 / 1573789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (852820749 / 1000000000) ≤ -Real.log (426211 / 1000000) ∧
    -Real.log (426211 / 1000000) ≤ (852820751 / 1000000000) := by
  have h := checkLog_sound (w := (73789 / 926211)) (n := 12)
    (lo := (159673569 / 1000000000)) (hi := (15967357 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 426211) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 426211) = 1/(426211 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-852820751 / 1000000000) (-852820749 / 1000000000) (Real.log (426211 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (113752477 / 250000000) ≤ -Real.log (1000000 / 1576189) ∧
    -Real.log (1000000 / 1576189) ≤ (455009909 / 1000000000) := by
  have h := checkLog_sound (w := (576189 / 2576189)) (n := 12)
    (lo := (113752477 / 250000000)) (hi := (455009909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1576189 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1576189 / 1000000) = 1/(1000000 / 1576189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (113752477 / 250000000) (455009909 / 1000000000) (Real.log (1576189 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1576189 / 1000000) = -Real.log (1000000 / 1576189) := by
    rw [show ((1576189 / 1000000) : ℝ) = ((1000000 / 1576189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (858467677 / 1000000000) ≤ -Real.log (423811 / 1000000) ∧
    -Real.log (423811 / 1000000) ≤ (858467679 / 1000000000) := by
  have h := checkLog_sound (w := (76189 / 923811)) (n := 12)
    (lo := (165320497 / 1000000000)) (hi := (82660249 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 423811) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 423811) = 1/(423811 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-858467679 / 1000000000) (-858467677 / 1000000000) (Real.log (423811 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (348702233 / 200000000) ≤ -Real.log (500000000000 / 2858691453809) ∧
    -Real.log (500000000000 / 2858691453809) ≤ (13621181 / 7812500) := by
  have h := checkLog_sound (w := (858691453809 / 4858691453809)) (n := 12)
    (lo := (71443361 / 200000000)) (hi := (178608403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2858691453809 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2858691453809 / 2000000000000) = 1/(500000000000 / 2858691453809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (348702233 / 200000000) (13621181 / 7812500) (Real.log (2858691453809 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2858691453809 / 500000000000) = -Real.log (500000000000 / 2858691453809) := by
    rw [show ((2858691453809 / 500000000000) : ℝ) = ((500000000000 / 2858691453809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (109528099 / 62500000) ≤ -Real.log (100000000000 / 576871634679) ∧
    -Real.log (100000000000 / 576871634679) ≤ (1752449587 / 1000000000) := by
  have h := checkLog_sound (w := (176871634679 / 976871634679)) (n := 12)
    (lo := (45769403 / 125000000)) (hi := (14646209 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((576871634679 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(576871634679 / 400000000000) = 1/(100000000000 / 576871634679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (109528099 / 62500000) (1752449587 / 1000000000) (Real.log (576871634679 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (576871634679 / 100000000000) = -Real.log (100000000000 / 576871634679) := by
    rw [show ((576871634679 / 100000000000) : ℝ) = ((100000000000 / 576871634679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1306306837 / 1000000000) ≤ -Real.log (125000000000 / 461563931949) ∧
    -Real.log (125000000000 / 461563931949) ≤ (1306306839 / 1000000000) := by
  have h := checkLog_sound (w := (211563931949 / 711563931949)) (n := 12)
    (lo := (613159657 / 1000000000)) (hi := (306579829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((461563931949 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(461563931949 / 250000000000) = 1/(125000000000 / 461563931949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1306306837 / 1000000000) (1306306839 / 1000000000) (Real.log (461563931949 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (461563931949 / 125000000000) = -Real.log (125000000000 / 461563931949) := by
    rw [show ((461563931949 / 125000000000) : ℝ) = ((125000000000 / 461563931949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (262695517 / 200000000) ≤ -Real.log (976562500 / 3631918639) ∧
    -Real.log (976562500 / 3631918639) ≤ (1313477587 / 1000000000) := by
  have h := checkLog_sound (w := (1678793639 / 5585043639)) (n := 12)
    (lo := (124066081 / 200000000)) (hi := (310165203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3631918639 / 1953125000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(3631918639 / 1953125000) = 1/(976562500 / 3631918639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (262695517 / 200000000) (1313477587 / 1000000000) (Real.log (3631918639 / 976562500)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3631918639 / 976562500) = -Real.log (976562500 / 3631918639) := by
    rw [show ((3631918639 / 976562500) : ℝ) = ((976562500 / 3631918639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0039
