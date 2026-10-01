import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0040
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

theorem reflection_log_1_neg : (382548261 / 1000000000) ≤ -Real.log (2560 / 3753) ∧
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


theorem reflection_log_1 : Bounds (382548261 / 1000000000) (191274131 / 500000000) (Real.log (3753 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3753 / 2560) = -Real.log (2560 / 3753) := by
    rw [show ((3753 / 2560) : ℝ) = ((2560 / 3753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (6273887 / 10000000) ≤ -Real.log (1367 / 2560) ∧
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


theorem reflection_log_2 : Bounds (-627388701 / 1000000000) (-6273887 / 10000000) (Real.log (1367 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (381748581 / 1000000000) ≤ -Real.log (256 / 375) ∧
    -Real.log (256 / 375) ≤ (190874291 / 500000000) := by
  have h := checkLog_sound (w := (119 / 631)) (n := 12)
    (lo := (381748581 / 1000000000)) (hi := (190874291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((375 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(375 / 256) = 1/(256 / 375) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (381748581 / 1000000000) (190874291 / 500000000) (Real.log (375 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (375 / 256) = -Real.log (256 / 375) := by
    rw [show ((375 / 256) : ℝ) = ((256 / 375) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (312598259 / 500000000) ≤ -Real.log (137 / 256) ∧
    -Real.log (137 / 256) ≤ (625196519 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 393)) (n := 12)
    (lo := (312598259 / 500000000)) (hi := (625196519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 137) = 1/(137 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-625196519 / 1000000000) (-312598259 / 500000000) (Real.log (137 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (65857191 / 100000000) ≤ -Real.log (1280 / 2473) ∧
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


theorem reflection_log_5 : Bounds (65857191 / 100000000) (658571911 / 1000000000) (Real.log (2473 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2473 / 1280) = -Real.log (1280 / 2473) := by
    rw [show ((2473 / 1280) : ℝ) = ((1280 / 2473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (672176809 / 250000000) ≤ -Real.log (87 / 1280) ∧
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


theorem reflection_log_6 : Bounds (-67217681 / 25000000) (-672176809 / 250000000) (Real.log (87 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (82169759 / 125000000) ≤ -Real.log (128 / 247) ∧
    -Real.log (128 / 247) ≤ (657358073 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 375)) (n := 12)
    (lo := (82169759 / 125000000)) (hi := (657358073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247 / 128) = 1/(128 / 247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (82169759 / 125000000) (657358073 / 1000000000) (Real.log (247 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (247 / 128) = -Real.log (128 / 247) := by
    rw [show ((247 / 128) : ℝ) = ((128 / 247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (663701421 / 250000000) ≤ -Real.log (9 / 128) ∧
    -Real.log (9 / 128) ≤ (331850711 / 125000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(16 / 9) = 1/(9 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-331850711 / 125000000) (-663701421 / 250000000) (Real.log (9 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (66330149 / 125000000) ≤ -Real.log (500000 / 850011) ∧
    -Real.log (500000 / 850011) ≤ (530641193 / 1000000000) := by
  have h := checkLog_sound (w := (350011 / 1350011)) (n := 12)
    (lo := (66330149 / 125000000)) (hi := (530641193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((850011 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(850011 / 500000) = 1/(500000 / 850011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (66330149 / 125000000) (530641193 / 1000000000) (Real.log (850011 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (850011 / 500000) = -Real.log (500000 / 850011) := by
    rw [show ((850011 / 500000) : ℝ) = ((500000 / 850011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1204046139 / 1000000000) ≤ -Real.log (149989 / 500000) ∧
    -Real.log (149989 / 500000) ≤ (1204046141 / 1000000000) := by
  have h := checkLog_sound (w := (100011 / 399989)) (n := 12)
    (lo := (510898959 / 1000000000)) (hi := (6386237 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 149989) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 149989) = 1/(149989 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1204046141 / 1000000000) (-1204046139 / 1000000000) (Real.log (149989 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (33247519 / 62500000) ≤ -Real.log (500000 / 851133) ∧
    -Real.log (500000 / 851133) ≤ (106392061 / 200000000) := by
  have h := checkLog_sound (w := (351133 / 1351133)) (n := 12)
    (lo := (33247519 / 62500000)) (hi := (106392061 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851133 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851133 / 500000) = 1/(500000 / 851133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (33247519 / 62500000) (106392061 / 200000000) (Real.log (851133 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (851133 / 500000) = -Real.log (500000 / 851133) := by
    rw [show ((851133 / 500000) : ℝ) = ((500000 / 851133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1211554807 / 1000000000) ≤ -Real.log (148867 / 500000) ∧
    -Real.log (148867 / 500000) ≤ (1211554809 / 1000000000) := by
  have h := checkLog_sound (w := (101133 / 398867)) (n := 12)
    (lo := (518407627 / 1000000000)) (hi := (129601907 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 148867) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 148867) = 1/(148867 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1211554809 / 1000000000) (-1211554807 / 1000000000) (Real.log (148867 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (451972669 / 1000000000) ≤ -Real.log (1000000 / 1571409) ∧
    -Real.log (1000000 / 1571409) ≤ (45197267 / 100000000) := by
  have h := checkLog_sound (w := (571409 / 2571409)) (n := 12)
    (lo := (451972669 / 1000000000)) (hi := (45197267 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1571409 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1571409 / 1000000) = 1/(1000000 / 1571409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (451972669 / 1000000000) (45197267 / 100000000) (Real.log (1571409 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1571409 / 1000000) = -Real.log (1000000 / 1571409) := by
    rw [show ((1571409 / 1000000) : ℝ) = ((1000000 / 1571409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (423626097 / 500000000) ≤ -Real.log (428591 / 1000000) ∧
    -Real.log (428591 / 1000000) ≤ (211813049 / 250000000) := by
  have h := checkLog_sound (w := (71409 / 928591)) (n := 12)
    (lo := (77052507 / 500000000)) (hi := (30821003 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 428591) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 428591) = 1/(428591 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-211813049 / 250000000) (-423626097 / 500000000) (Real.log (428591 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (453486723 / 1000000000) ≤ -Real.log (100000 / 157379) ∧
    -Real.log (100000 / 157379) ≤ (113371681 / 250000000) := by
  have h := checkLog_sound (w := (57379 / 257379)) (n := 12)
    (lo := (453486723 / 1000000000)) (hi := (113371681 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157379 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157379 / 100000) = 1/(100000 / 157379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (453486723 / 1000000000) (113371681 / 250000000) (Real.log (157379 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (157379 / 100000) = -Real.log (100000 / 157379) := by
    rw [show ((157379 / 100000) : ℝ) = ((100000 / 157379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (170564619 / 200000000) ≤ -Real.log (42621 / 100000) ∧
    -Real.log (42621 / 100000) ≤ (852823097 / 1000000000) := by
  have h := checkLog_sound (w := (7379 / 92621)) (n := 12)
    (lo := (31935183 / 200000000)) (hi := (39918979 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 42621) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 42621) = 1/(42621 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-852823097 / 1000000000) (-170564619 / 200000000) (Real.log (42621 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1734687331 / 1000000000) ≤ -Real.log (100000000000 / 566715559141) ∧
    -Real.log (100000000000 / 566715559141) ≤ (867343667 / 500000000) := by
  have h := checkLog_sound (w := (166715559141 / 966715559141)) (n := 12)
    (lo := (348392971 / 1000000000)) (hi := (87098243 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((566715559141 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(566715559141 / 400000000000) = 1/(100000000000 / 566715559141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1734687331 / 1000000000) (867343667 / 500000000) (Real.log (566715559141 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (566715559141 / 100000000000) = -Real.log (100000000000 / 566715559141) := by
    rw [show ((566715559141 / 100000000000) : ℝ) = ((100000000000 / 566715559141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (217939389 / 125000000) ≤ -Real.log (7812500000 / 44667230229) ∧
    -Real.log (7812500000 / 44667230229) ≤ (348703023 / 200000000) := by
  have h := checkLog_sound (w := (13417230229 / 75917230229)) (n := 12)
    (lo := (22326297 / 62500000)) (hi := (357220753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44667230229 / 31250000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(44667230229 / 31250000000) = 1/(7812500000 / 44667230229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (217939389 / 125000000) (348703023 / 200000000) (Real.log (44667230229 / 7812500000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (44667230229 / 7812500000) = -Real.log (7812500000 / 44667230229) := by
    rw [show ((44667230229 / 7812500000) : ℝ) = ((7812500000 / 44667230229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1299224863 / 1000000000) ≤ -Real.log (500000000000 / 1833226782643) ∧
    -Real.log (500000000000 / 1833226782643) ≤ (259844973 / 200000000) := by
  have h := checkLog_sound (w := (833226782643 / 2833226782643)) (n := 12)
    (lo := (606077683 / 1000000000)) (hi := (151519421 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1833226782643 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1833226782643 / 1000000000000) = 1/(500000000000 / 1833226782643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1299224863 / 1000000000) (259844973 / 200000000) (Real.log (1833226782643 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1833226782643 / 500000000000) = -Real.log (500000000000 / 1833226782643) := by
    rw [show ((1833226782643 / 500000000000) : ℝ) = ((500000000000 / 1833226782643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (653154909 / 500000000) ≤ -Real.log (250000000000 / 923130616363) ∧
    -Real.log (250000000000 / 923130616363) ≤ (65315491 / 50000000) := by
  have h := checkLog_sound (w := (423130616363 / 1423130616363)) (n := 12)
    (lo := (306581319 / 500000000)) (hi := (613162639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((923130616363 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(923130616363 / 500000000000) = 1/(250000000000 / 923130616363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (653154909 / 500000000) (65315491 / 50000000) (Real.log (923130616363 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (923130616363 / 250000000000) = -Real.log (250000000000 / 923130616363) := by
    rw [show ((923130616363 / 250000000000) : ℝ) = ((250000000000 / 923130616363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0040
