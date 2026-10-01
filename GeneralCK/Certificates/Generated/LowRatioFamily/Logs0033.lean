import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2112_neg : (41707683 / 125000000) ≤ -Real.log (125000000000 / 174508805559) ∧
    -Real.log (125000000000 / 174508805559) ≤ (66732293 / 200000000) := by
  have h := checkLog_sound (w := (49508805559 / 299508805559)) (n := 12)
    (lo := (41707683 / 125000000)) (hi := (66732293 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((174508805559 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(174508805559 / 125000000000) = 1/(125000000000 / 174508805559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2112 : Bounds (41707683 / 125000000) (66732293 / 200000000) (Real.log (174508805559 / 125000000000)) := by
  have h := reflection_log_2112_neg
  have he : Real.log (174508805559 / 125000000000) = -Real.log (125000000000 / 174508805559) := by
    rw [show ((174508805559 / 125000000000) : ℝ) = ((125000000000 / 174508805559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2113_neg : (244903 / 1600000) ≤ -Real.log (5000 / 5827) ∧
    -Real.log (5000 / 5827) ≤ (19133047 / 125000000) := by
  have h := checkLog_sound (w := (827 / 10827)) (n := 12)
    (lo := (244903 / 1600000)) (hi := (19133047 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5827 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5827 / 5000) = 1/(5000 / 5827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2113 : Bounds (244903 / 1600000) (19133047 / 125000000) (Real.log (5827 / 5000)) := by
  have h := reflection_log_2113_neg
  have he : Real.log (5827 / 5000) = -Real.log (5000 / 5827) := by
    rw [show ((5827 / 5000) : ℝ) = ((5000 / 5827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2114_neg : (18080271 / 100000000) ≤ -Real.log (4173 / 5000) ∧
    -Real.log (4173 / 5000) ≤ (180802711 / 1000000000) := by
  have h := checkLog_sound (w := (827 / 9173)) (n := 12)
    (lo := (18080271 / 100000000)) (hi := (180802711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4173) = 1/(4173 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2114 : Bounds (-180802711 / 1000000000) (-18080271 / 100000000) (Real.log (4173 / 5000)) := by
  have h := reflection_log_2114_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2115_neg : (82693 / 500000000) ≤ -Real.log (5000000 / 5000827) ∧
    -Real.log (5000000 / 5000827) ≤ (165387 / 1000000000) := by
  have h := checkLog_sound (w := (827 / 10000827)) (n := 12)
    (lo := (82693 / 500000000)) (hi := (165387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000827 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000827 / 5000000) = 1/(5000000 / 5000827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2115 : Bounds (82693 / 500000000) (165387 / 1000000000) (Real.log (5000827 / 5000000)) := by
  have h := reflection_log_2115_neg
  have he : Real.log (5000827 / 5000000) = -Real.log (5000000 / 5000827) := by
    rw [show ((5000827 / 5000000) : ℝ) = ((5000000 / 5000827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2116_neg : (165413 / 1000000000) ≤ -Real.log (4999173 / 5000000) ∧
    -Real.log (4999173 / 5000000) ≤ (82707 / 500000000) := by
  have h := checkLog_sound (w := (827 / 9999173)) (n := 12)
    (lo := (165413 / 1000000000)) (hi := (82707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999173) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999173) = 1/(4999173 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2116 : Bounds (-82707 / 500000000) (-165413 / 1000000000) (Real.log (4999173 / 5000000)) := by
  have h := reflection_log_2116_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2117_neg : (79714653 / 1000000000) ≤ -Real.log (500000 / 541489) ∧
    -Real.log (500000 / 541489) ≤ (39857327 / 500000000) := by
  have h := checkLog_sound (w := (41489 / 1041489)) (n := 12)
    (lo := (79714653 / 1000000000)) (hi := (39857327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541489 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541489 / 500000) = 1/(500000 / 541489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2117 : Bounds (79714653 / 1000000000) (39857327 / 500000000) (Real.log (541489 / 500000)) := by
  have h := reflection_log_2117_neg
  have he : Real.log (541489 / 500000) = -Real.log (500000 / 541489) := by
    rw [show ((541489 / 500000) : ℝ) = ((500000 / 541489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2118_neg : (17324763 / 200000000) ≤ -Real.log (458511 / 500000) ∧
    -Real.log (458511 / 500000) ≤ (10827977 / 125000000) := by
  have h := checkLog_sound (w := (41489 / 958511)) (n := 12)
    (lo := (17324763 / 200000000)) (hi := (10827977 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458511) = 1/(458511 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2118 : Bounds (-10827977 / 125000000) (-17324763 / 200000000) (Real.log (458511 / 500000)) := by
  have h := reflection_log_2118_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2119_neg : (19978521 / 250000000) ≤ -Real.log (500000 / 541597) ∧
    -Real.log (500000 / 541597) ≤ (15982817 / 200000000) := by
  have h := checkLog_sound (w := (41597 / 1041597)) (n := 12)
    (lo := (19978521 / 250000000)) (hi := (15982817 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541597 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541597 / 500000) = 1/(500000 / 541597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2119 : Bounds (19978521 / 250000000) (15982817 / 200000000) (Real.log (541597 / 500000)) := by
  have h := reflection_log_2119_neg
  have he : Real.log (541597 / 500000) = -Real.log (500000 / 541597) := by
    rw [show ((541597 / 500000) : ℝ) = ((500000 / 541597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2120_neg : (21714847 / 250000000) ≤ -Real.log (458403 / 500000) ∧
    -Real.log (458403 / 500000) ≤ (86859389 / 1000000000) := by
  have h := checkLog_sound (w := (41597 / 958403)) (n := 12)
    (lo := (21714847 / 250000000)) (hi := (86859389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458403) = 1/(458403 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2120 : Bounds (-86859389 / 1000000000) (-21714847 / 250000000) (Real.log (458403 / 500000)) := by
  have h := reflection_log_2120_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2121_neg : (868163 / 125000000) ≤ -Real.log (248269689591 / 250000000000) ∧
    -Real.log (248269689591 / 250000000000) ≤ (1389061 / 200000000) := by
  have h := checkLog_sound (w := (1730310409 / 498269689591)) (n := 12)
    (lo := (868163 / 125000000)) (hi := (1389061 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248269689591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248269689591) = 1/(248269689591 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2121 : Bounds (-1389061 / 200000000) (-868163 / 125000000) (Real.log (248269689591 / 250000000000)) := by
  have h := reflection_log_2121_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2122_neg : (6909161 / 1000000000) ≤ -Real.log (248278662879 / 250000000000) ∧
    -Real.log (248278662879 / 250000000000) ≤ (3454581 / 500000000) := by
  have h := checkLog_sound (w := (1721337121 / 498278662879)) (n := 12)
    (lo := (6909161 / 1000000000)) (hi := (3454581 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248278662879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248278662879) = 1/(248278662879 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2122 : Bounds (-3454581 / 500000000) (-6909161 / 1000000000) (Real.log (248278662879 / 250000000000)) := by
  have h := reflection_log_2122_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2123_neg : (166338469 / 1000000000) ≤ -Real.log (250000000000 / 295243189367) ∧
    -Real.log (250000000000 / 295243189367) ≤ (16633847 / 100000000) := by
  have h := checkLog_sound (w := (45243189367 / 545243189367)) (n := 12)
    (lo := (166338469 / 1000000000)) (hi := (16633847 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295243189367 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295243189367 / 250000000000) = 1/(250000000000 / 295243189367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2123 : Bounds (166338469 / 1000000000) (16633847 / 100000000) (Real.log (295243189367 / 250000000000)) := by
  have h := reflection_log_2123_neg
  have he : Real.log (295243189367 / 250000000000) = -Real.log (250000000000 / 295243189367) := by
    rw [show ((295243189367 / 250000000000) : ℝ) = ((250000000000 / 295243189367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2124_neg : (5211671 / 31250000) ≤ -Real.log (62500000000 / 73842912241) ∧
    -Real.log (62500000000 / 73842912241) ≤ (166773473 / 1000000000) := by
  have h := checkLog_sound (w := (11342912241 / 136342912241)) (n := 12)
    (lo := (5211671 / 31250000)) (hi := (166773473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73842912241 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73842912241 / 62500000000) = 1/(62500000000 / 73842912241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2124 : Bounds (5211671 / 31250000) (166773473 / 1000000000) (Real.log (73842912241 / 62500000000)) := by
  have h := reflection_log_2124_neg
  have he : Real.log (73842912241 / 62500000000) = -Real.log (62500000000 / 73842912241) := by
    rw [show ((73842912241 / 62500000000) : ℝ) = ((62500000000 / 73842912241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2125_neg : (41707683 / 125000000) ≤ -Real.log (100000000000 / 139607044447) ∧
    -Real.log (100000000000 / 139607044447) ≤ (66732293 / 200000000) := by
  have h := checkLog_sound (w := (39607044447 / 239607044447)) (n := 12)
    (lo := (41707683 / 125000000)) (hi := (66732293 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139607044447 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139607044447 / 100000000000) = 1/(100000000000 / 139607044447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2125 : Bounds (41707683 / 125000000) (66732293 / 200000000) (Real.log (139607044447 / 100000000000)) := by
  have h := reflection_log_2125_neg
  have he : Real.log (139607044447 / 100000000000) = -Real.log (100000000000 / 139607044447) := by
    rw [show ((139607044447 / 100000000000) : ℝ) = ((100000000000 / 139607044447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2126_neg : (166933543 / 500000000) ≤ -Real.log (500000000000 / 698178768273) ∧
    -Real.log (500000000000 / 698178768273) ≤ (333867087 / 1000000000) := by
  have h := checkLog_sound (w := (198178768273 / 1198178768273)) (n := 12)
    (lo := (166933543 / 500000000)) (hi := (333867087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((698178768273 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(698178768273 / 500000000000) = 1/(500000000000 / 698178768273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2126 : Bounds (166933543 / 500000000) (333867087 / 1000000000) (Real.log (698178768273 / 500000000000)) := by
  have h := reflection_log_2126_neg
  have he : Real.log (698178768273 / 500000000000) = -Real.log (500000000000 / 698178768273) := by
    rw [show ((698178768273 / 500000000000) : ℝ) = ((500000000000 / 698178768273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2127_neg : (153150179 / 1000000000) ≤ -Real.log (2000 / 2331) ∧
    -Real.log (2000 / 2331) ≤ (7657509 / 50000000) := by
  have h := checkLog_sound (w := (331 / 4331)) (n := 12)
    (lo := (153150179 / 1000000000)) (hi := (7657509 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2331 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2331 / 2000) = 1/(2000 / 2331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2127 : Bounds (153150179 / 1000000000) (7657509 / 50000000) (Real.log (2331 / 2000)) := by
  have h := reflection_log_2127_neg
  have he : Real.log (2331 / 2000) = -Real.log (2000 / 2331) := by
    rw [show ((2331 / 2000) : ℝ) = ((2000 / 2331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2128_neg : (36184507 / 200000000) ≤ -Real.log (1669 / 2000) ∧
    -Real.log (1669 / 2000) ≤ (22615317 / 125000000) := by
  have h := checkLog_sound (w := (331 / 3669)) (n := 12)
    (lo := (36184507 / 200000000)) (hi := (22615317 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1669) = 1/(1669 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2128 : Bounds (-22615317 / 125000000) (-36184507 / 200000000) (Real.log (1669 / 2000)) := by
  have h := reflection_log_2128_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2129_neg : (82743 / 500000000) ≤ -Real.log (2000000 / 2000331) ∧
    -Real.log (2000000 / 2000331) ≤ (165487 / 1000000000) := by
  have h := checkLog_sound (w := (331 / 4000331)) (n := 12)
    (lo := (82743 / 500000000)) (hi := (165487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000331 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000331 / 2000000) = 1/(2000000 / 2000331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2129 : Bounds (82743 / 500000000) (165487 / 1000000000) (Real.log (2000331 / 2000000)) := by
  have h := reflection_log_2129_neg
  have he : Real.log (2000331 / 2000000) = -Real.log (2000000 / 2000331) := by
    rw [show ((2000331 / 2000000) : ℝ) = ((2000000 / 2000331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2130_neg : (165513 / 1000000000) ≤ -Real.log (1999669 / 2000000) ∧
    -Real.log (1999669 / 2000000) ≤ (82757 / 500000000) := by
  have h := checkLog_sound (w := (331 / 3999669)) (n := 12)
    (lo := (165513 / 1000000000)) (hi := (82757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999669) = 1/(1999669 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2130 : Bounds (-82757 / 500000000) (-165513 / 1000000000) (Real.log (1999669 / 2000000)) := by
  have h := reflection_log_2130_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2131_neg : (15952349 / 200000000) ≤ -Real.log (1000000 / 1083029) ∧
    -Real.log (1000000 / 1083029) ≤ (39880873 / 500000000) := by
  have h := checkLog_sound (w := (83029 / 2083029)) (n := 12)
    (lo := (15952349 / 200000000)) (hi := (39880873 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083029 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083029 / 1000000) = 1/(1000000 / 1083029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2131 : Bounds (15952349 / 200000000) (39880873 / 500000000) (Real.log (1083029 / 1000000)) := by
  have h := reflection_log_2131_neg
  have he : Real.log (1083029 / 1000000) = -Real.log (1000000 / 1083029) := by
    rw [show ((1083029 / 1000000) : ℝ) = ((1000000 / 1083029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2132_neg : (10834929 / 125000000) ≤ -Real.log (916971 / 1000000) ∧
    -Real.log (916971 / 1000000) ≤ (86679433 / 1000000000) := by
  have h := checkLog_sound (w := (83029 / 1916971)) (n := 12)
    (lo := (10834929 / 125000000)) (hi := (86679433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916971) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916971) = 1/(916971 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2132 : Bounds (-86679433 / 1000000000) (-10834929 / 125000000) (Real.log (916971 / 1000000)) := by
  have h := reflection_log_2132_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2133_neg : (15992233 / 200000000) ≤ -Real.log (200000 / 216649) ∧
    -Real.log (200000 / 216649) ≤ (39980583 / 500000000) := by
  have h := checkLog_sound (w := (16649 / 416649)) (n := 12)
    (lo := (15992233 / 200000000)) (hi := (39980583 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216649 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216649 / 200000) = 1/(200000 / 216649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2133 : Bounds (15992233 / 200000000) (39980583 / 500000000) (Real.log (216649 / 200000)) := by
  have h := reflection_log_2133_neg
  have he : Real.log (216649 / 200000) = -Real.log (200000 / 216649) := by
    rw [show ((216649 / 200000) : ℝ) = ((200000 / 216649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2134_neg : (86915017 / 1000000000) ≤ -Real.log (183351 / 200000) ∧
    -Real.log (183351 / 200000) ≤ (43457509 / 500000000) := by
  have h := checkLog_sound (w := (16649 / 383351)) (n := 12)
    (lo := (86915017 / 1000000000)) (hi := (43457509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183351) = 1/(183351 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2134 : Bounds (-43457509 / 500000000) (-86915017 / 1000000000) (Real.log (183351 / 200000)) := by
  have h := reflection_log_2134_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2135_neg : (1738463 / 250000000) ≤ -Real.log (39722810799 / 40000000000) ∧
    -Real.log (39722810799 / 40000000000) ≤ (6953853 / 1000000000) := by
  have h := checkLog_sound (w := (277189201 / 79722810799)) (n := 12)
    (lo := (1738463 / 250000000)) (hi := (6953853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39722810799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39722810799) = 1/(39722810799 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2135 : Bounds (-6953853 / 1000000000) (-1738463 / 250000000) (Real.log (39722810799 / 40000000000)) := by
  have h := reflection_log_2135_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2136_neg : (3458843 / 500000000) ≤ -Real.log (993106185159 / 1000000000000) ∧
    -Real.log (993106185159 / 1000000000000) ≤ (6917687 / 1000000000) := by
  have h := checkLog_sound (w := (6893814841 / 1993106185159)) (n := 12)
    (lo := (3458843 / 500000000)) (hi := (6917687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993106185159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993106185159) = 1/(993106185159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2136 : Bounds (-6917687 / 1000000000) (-3458843 / 500000000) (Real.log (993106185159 / 1000000000000)) := by
  have h := reflection_log_2136_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2137_neg : (166441177 / 1000000000) ≤ -Real.log (100000000000 / 118109405859) ∧
    -Real.log (100000000000 / 118109405859) ≤ (83220589 / 500000000) := by
  have h := checkLog_sound (w := (18109405859 / 218109405859)) (n := 12)
    (lo := (166441177 / 1000000000)) (hi := (83220589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118109405859 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118109405859 / 100000000000) = 1/(100000000000 / 118109405859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2137 : Bounds (166441177 / 1000000000) (83220589 / 500000000) (Real.log (118109405859 / 100000000000)) := by
  have h := reflection_log_2137_neg
  have he : Real.log (118109405859 / 100000000000) = -Real.log (100000000000 / 118109405859) := by
    rw [show ((118109405859 / 100000000000) : ℝ) = ((100000000000 / 118109405859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2138_neg : (166876183 / 1000000000) ≤ -Real.log (31250000000 / 36925248567) ∧
    -Real.log (31250000000 / 36925248567) ≤ (20859523 / 125000000) := by
  have h := checkLog_sound (w := (5675248567 / 68175248567)) (n := 12)
    (lo := (166876183 / 1000000000)) (hi := (20859523 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36925248567 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36925248567 / 31250000000) = 1/(31250000000 / 36925248567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2138 : Bounds (166876183 / 1000000000) (20859523 / 125000000) (Real.log (36925248567 / 31250000000)) := by
  have h := reflection_log_2138_neg
  have he : Real.log (36925248567 / 31250000000) = -Real.log (31250000000 / 36925248567) := by
    rw [show ((36925248567 / 31250000000) : ℝ) = ((31250000000 / 36925248567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2139_neg : (166933543 / 500000000) ≤ -Real.log (31250000000 / 43636173017) ∧
    -Real.log (31250000000 / 43636173017) ≤ (333867087 / 1000000000) := by
  have h := checkLog_sound (w := (12386173017 / 74886173017)) (n := 12)
    (lo := (166933543 / 500000000)) (hi := (333867087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43636173017 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43636173017 / 31250000000) = 1/(31250000000 / 43636173017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2139 : Bounds (166933543 / 500000000) (333867087 / 1000000000) (Real.log (43636173017 / 31250000000)) := by
  have h := reflection_log_2139_neg
  have he : Real.log (43636173017 / 31250000000) = -Real.log (31250000000 / 43636173017) := by
    rw [show ((43636173017 / 31250000000) : ℝ) = ((31250000000 / 43636173017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2140_neg : (66814543 / 200000000) ≤ -Real.log (62500000000 / 87290293589) ∧
    -Real.log (62500000000 / 87290293589) ≤ (83518179 / 250000000) := by
  have h := checkLog_sound (w := (24790293589 / 149790293589)) (n := 12)
    (lo := (66814543 / 200000000)) (hi := (83518179 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87290293589 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87290293589 / 62500000000) = 1/(62500000000 / 87290293589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2140 : Bounds (66814543 / 200000000) (83518179 / 250000000) (Real.log (87290293589 / 62500000000)) := by
  have h := reflection_log_2140_neg
  have he : Real.log (87290293589 / 62500000000) = -Real.log (62500000000 / 87290293589) := by
    rw [show ((87290293589 / 62500000000) : ℝ) = ((62500000000 / 87290293589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2141_neg : (6129439 / 40000000) ≤ -Real.log (1250 / 1457) ∧
    -Real.log (1250 / 1457) ≤ (19154497 / 125000000) := by
  have h := checkLog_sound (w := (207 / 2707)) (n := 12)
    (lo := (6129439 / 40000000)) (hi := (19154497 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1457 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1457 / 1250) = 1/(1250 / 1457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2141 : Bounds (6129439 / 40000000) (19154497 / 125000000) (Real.log (1457 / 1250)) := by
  have h := reflection_log_2141_neg
  have he : Real.log (1457 / 1250) = -Real.log (1250 / 1457) := by
    rw [show ((1457 / 1250) : ℝ) = ((1250 / 1457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2142_neg : (1448339 / 8000000) ≤ -Real.log (1043 / 1250) ∧
    -Real.log (1043 / 1250) ≤ (22630297 / 125000000) := by
  have h := checkLog_sound (w := (207 / 2293)) (n := 12)
    (lo := (1448339 / 8000000)) (hi := (22630297 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1043) = 1/(1043 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2142 : Bounds (-22630297 / 125000000) (-1448339 / 8000000) (Real.log (1043 / 1250)) := by
  have h := reflection_log_2142_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2143_neg : (82793 / 500000000) ≤ -Real.log (1250000 / 1250207) ∧
    -Real.log (1250000 / 1250207) ≤ (165587 / 1000000000) := by
  have h := checkLog_sound (w := (207 / 2500207)) (n := 12)
    (lo := (82793 / 500000000)) (hi := (165587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250207 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250207 / 1250000) = 1/(1250000 / 1250207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2143 : Bounds (82793 / 500000000) (165587 / 1000000000) (Real.log (1250207 / 1250000)) := by
  have h := reflection_log_2143_neg
  have he : Real.log (1250207 / 1250000) = -Real.log (1250000 / 1250207) := by
    rw [show ((1250207 / 1250000) : ℝ) = ((1250000 / 1250207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2144_neg : (165613 / 1000000000) ≤ -Real.log (1249793 / 1250000) ∧
    -Real.log (1249793 / 1250000) ≤ (82807 / 500000000) := by
  have h := checkLog_sound (w := (207 / 2499793)) (n := 12)
    (lo := (165613 / 1000000000)) (hi := (82807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249793) = 1/(1249793 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2144 : Bounds (-82807 / 500000000) (-165613 / 1000000000) (Real.log (1249793 / 1250000)) := by
  have h := reflection_log_2144_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2145_neg : (7980791 / 100000000) ≤ -Real.log (1000000 / 1083079) ∧
    -Real.log (1000000 / 1083079) ≤ (79807911 / 1000000000) := by
  have h := checkLog_sound (w := (83079 / 2083079)) (n := 12)
    (lo := (7980791 / 100000000)) (hi := (79807911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083079 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083079 / 1000000) = 1/(1000000 / 1083079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2145 : Bounds (7980791 / 100000000) (79807911 / 1000000000) (Real.log (1083079 / 1000000)) := by
  have h := reflection_log_2145_neg
  have he : Real.log (1083079 / 1000000) = -Real.log (1000000 / 1083079) := by
    rw [show ((1083079 / 1000000) : ℝ) = ((1000000 / 1083079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2146_neg : (2168349 / 25000000) ≤ -Real.log (916921 / 1000000) ∧
    -Real.log (916921 / 1000000) ≤ (86733961 / 1000000000) := by
  have h := checkLog_sound (w := (83079 / 1916921)) (n := 12)
    (lo := (2168349 / 25000000)) (hi := (86733961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916921) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916921) = 1/(916921 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2146 : Bounds (-86733961 / 1000000000) (-2168349 / 25000000) (Real.log (916921 / 1000000)) := by
  have h := reflection_log_2146_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2147_neg : (16001649 / 200000000) ≤ -Real.log (31250 / 33853) ∧
    -Real.log (31250 / 33853) ≤ (40004123 / 500000000) := by
  have h := checkLog_sound (w := (2603 / 65103)) (n := 12)
    (lo := (16001649 / 200000000)) (hi := (40004123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33853 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33853 / 31250) = 1/(31250 / 33853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2147 : Bounds (16001649 / 200000000) (40004123 / 500000000) (Real.log (33853 / 31250)) := by
  have h := reflection_log_2147_neg
  have he : Real.log (33853 / 31250) = -Real.log (31250 / 33853) := by
    rw [show ((33853 / 31250) : ℝ) = ((31250 / 33853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2148_neg : (1739413 / 20000000) ≤ -Real.log (28647 / 31250) ∧
    -Real.log (28647 / 31250) ≤ (86970651 / 1000000000) := by
  have h := checkLog_sound (w := (2603 / 59897)) (n := 12)
    (lo := (1739413 / 20000000)) (hi := (86970651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 28647) = 1/(28647 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2148 : Bounds (-86970651 / 1000000000) (-1739413 / 20000000) (Real.log (28647 / 31250)) := by
  have h := reflection_log_2148_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2149_neg : (1392481 / 200000000) ≤ -Real.log (969786891 / 976562500) ∧
    -Real.log (969786891 / 976562500) ≤ (3481203 / 500000000) := by
  have h := checkLog_sound (w := (6775609 / 1946349391)) (n := 12)
    (lo := (1392481 / 200000000)) (hi := (3481203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 969786891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 969786891) = 1/(969786891 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2149 : Bounds (-3481203 / 500000000) (-1392481 / 200000000) (Real.log (969786891 / 976562500)) := by
  have h := reflection_log_2149_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2150_neg : (138521 / 20000000) ≤ -Real.log (993097879759 / 1000000000000) ∧
    -Real.log (993097879759 / 1000000000000) ≤ (6926051 / 1000000000) := by
  have h := checkLog_sound (w := (6902120241 / 1993097879759)) (n := 12)
    (lo := (138521 / 20000000)) (hi := (6926051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993097879759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993097879759) = 1/(993097879759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2150 : Bounds (-6926051 / 1000000000) (-138521 / 20000000) (Real.log (993097879759 / 1000000000000)) := by
  have h := reflection_log_2150_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2151_neg : (166541871 / 1000000000) ≤ -Real.log (500000000000 / 590606497179) ∧
    -Real.log (500000000000 / 590606497179) ≤ (10408867 / 62500000) := by
  have h := checkLog_sound (w := (90606497179 / 1090606497179)) (n := 12)
    (lo := (166541871 / 1000000000)) (hi := (10408867 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590606497179 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590606497179 / 500000000000) = 1/(500000000000 / 590606497179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2151 : Bounds (166541871 / 1000000000) (10408867 / 62500000) (Real.log (590606497179 / 500000000000)) := by
  have h := reflection_log_2151_neg
  have he : Real.log (590606497179 / 500000000000) = -Real.log (500000000000 / 590606497179) := by
    rw [show ((590606497179 / 500000000000) : ℝ) = ((500000000000 / 590606497179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2152_neg : (10436181 / 62500000) ≤ -Real.log (500000000000 / 590864662967) ∧
    -Real.log (500000000000 / 590864662967) ≤ (166978897 / 1000000000) := by
  have h := checkLog_sound (w := (90864662967 / 1090864662967)) (n := 12)
    (lo := (10436181 / 62500000)) (hi := (166978897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590864662967 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590864662967 / 500000000000) = 1/(500000000000 / 590864662967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2152 : Bounds (10436181 / 62500000) (166978897 / 1000000000) (Real.log (590864662967 / 500000000000)) := by
  have h := reflection_log_2152_neg
  have he : Real.log (590864662967 / 500000000000) = -Real.log (500000000000 / 590864662967) := by
    rw [show ((590864662967 / 500000000000) : ℝ) = ((500000000000 / 590864662967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2153_neg : (66814543 / 200000000) ≤ -Real.log (500000000000 / 698322348711) ∧
    -Real.log (500000000000 / 698322348711) ≤ (83518179 / 250000000) := by
  have h := checkLog_sound (w := (198322348711 / 1198322348711)) (n := 12)
    (lo := (66814543 / 200000000)) (hi := (83518179 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((698322348711 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(698322348711 / 500000000000) = 1/(500000000000 / 698322348711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2153 : Bounds (66814543 / 200000000) (83518179 / 250000000) (Real.log (698322348711 / 500000000000)) := by
  have h := reflection_log_2153_neg
  have he : Real.log (698322348711 / 500000000000) = -Real.log (500000000000 / 698322348711) := by
    rw [show ((698322348711 / 500000000000) : ℝ) = ((500000000000 / 698322348711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2154_neg : (334278351 / 1000000000) ≤ -Real.log (500000000000 / 698465963567) ∧
    -Real.log (500000000000 / 698465963567) ≤ (20892397 / 62500000) := by
  have h := checkLog_sound (w := (198465963567 / 1198465963567)) (n := 12)
    (lo := (334278351 / 1000000000)) (hi := (20892397 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((698465963567 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(698465963567 / 500000000000) = 1/(500000000000 / 698465963567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2154 : Bounds (334278351 / 1000000000) (20892397 / 62500000) (Real.log (698465963567 / 500000000000)) := by
  have h := reflection_log_2154_neg
  have he : Real.log (698465963567 / 500000000000) = -Real.log (500000000000 / 698465963567) := by
    rw [show ((698465963567 / 500000000000) : ℝ) = ((500000000000 / 698465963567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2155_neg : (38330441 / 250000000) ≤ -Real.log (10000 / 11657) ∧
    -Real.log (10000 / 11657) ≤ (30664353 / 200000000) := by
  have h := checkLog_sound (w := (1657 / 21657)) (n := 12)
    (lo := (38330441 / 250000000)) (hi := (30664353 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11657 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11657 / 10000) = 1/(10000 / 11657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2155 : Bounds (38330441 / 250000000) (30664353 / 200000000) (Real.log (11657 / 10000)) := by
  have h := reflection_log_2155_neg
  have he : Real.log (11657 / 10000) = -Real.log (10000 / 11657) := by
    rw [show ((11657 / 10000) : ℝ) = ((10000 / 11657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2156_neg : (181162229 / 1000000000) ≤ -Real.log (8343 / 10000) ∧
    -Real.log (8343 / 10000) ≤ (18116223 / 100000000) := by
  have h := checkLog_sound (w := (1657 / 18343)) (n := 12)
    (lo := (181162229 / 1000000000)) (hi := (18116223 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8343) = 1/(8343 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2156 : Bounds (-18116223 / 100000000) (-181162229 / 1000000000) (Real.log (8343 / 10000)) := by
  have h := reflection_log_2156_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2157_neg : (82843 / 500000000) ≤ -Real.log (10000000 / 10001657) ∧
    -Real.log (10000000 / 10001657) ≤ (165687 / 1000000000) := by
  have h := checkLog_sound (w := (1657 / 20001657)) (n := 12)
    (lo := (82843 / 500000000)) (hi := (165687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001657 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001657 / 10000000) = 1/(10000000 / 10001657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2157 : Bounds (82843 / 500000000) (165687 / 1000000000) (Real.log (10001657 / 10000000)) := by
  have h := reflection_log_2157_neg
  have he : Real.log (10001657 / 10000000) = -Real.log (10000000 / 10001657) := by
    rw [show ((10001657 / 10000000) : ℝ) = ((10000000 / 10001657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2158_neg : (165713 / 1000000000) ≤ -Real.log (9998343 / 10000000) ∧
    -Real.log (9998343 / 10000000) ≤ (82857 / 500000000) := by
  have h := checkLog_sound (w := (1657 / 19998343)) (n := 12)
    (lo := (165713 / 1000000000)) (hi := (82857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998343) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998343) = 1/(9998343 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2158 : Bounds (-82857 / 500000000) (-165713 / 1000000000) (Real.log (9998343 / 10000000)) := by
  have h := reflection_log_2158_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2159_neg : (79854997 / 1000000000) ≤ -Real.log (100000 / 108313) ∧
    -Real.log (100000 / 108313) ≤ (39927499 / 500000000) := by
  have h := checkLog_sound (w := (8313 / 208313)) (n := 12)
    (lo := (79854997 / 1000000000)) (hi := (39927499 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108313 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108313 / 100000) = 1/(100000 / 108313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2159 : Bounds (79854997 / 1000000000) (39927499 / 500000000) (Real.log (108313 / 100000)) := by
  have h := reflection_log_2159_neg
  have he : Real.log (108313 / 100000) = -Real.log (100000 / 108313) := by
    rw [show ((108313 / 100000) : ℝ) = ((100000 / 108313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2160_neg : (86789583 / 1000000000) ≤ -Real.log (91687 / 100000) ∧
    -Real.log (91687 / 100000) ≤ (5424349 / 62500000) := by
  have h := checkLog_sound (w := (8313 / 191687)) (n := 12)
    (lo := (86789583 / 1000000000)) (hi := (5424349 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 91687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 91687) = 1/(91687 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2160 : Bounds (-5424349 / 62500000) (-86789583 / 1000000000) (Real.log (91687 / 100000)) := by
  have h := reflection_log_2160_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2161_neg : (80054399 / 1000000000) ≤ -Real.log (500000 / 541673) ∧
    -Real.log (500000 / 541673) ≤ (25017 / 312500) := by
  have h := checkLog_sound (w := (41673 / 1041673)) (n := 12)
    (lo := (80054399 / 1000000000)) (hi := (25017 / 312500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541673 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541673 / 500000) = 1/(500000 / 541673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2161 : Bounds (80054399 / 1000000000) (25017 / 312500) (Real.log (541673 / 500000)) := by
  have h := reflection_log_2161_neg
  have he : Real.log (541673 / 500000) = -Real.log (500000 / 541673) := by
    rw [show ((541673 / 500000) : ℝ) = ((500000 / 541673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2162_neg : (17405039 / 200000000) ≤ -Real.log (458327 / 500000) ∧
    -Real.log (458327 / 500000) ≤ (21756299 / 250000000) := by
  have h := checkLog_sound (w := (41673 / 958327)) (n := 12)
    (lo := (17405039 / 200000000)) (hi := (21756299 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458327) = 1/(458327 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2162 : Bounds (-21756299 / 250000000) (-17405039 / 200000000) (Real.log (458327 / 500000)) := by
  have h := reflection_log_2162_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2163_neg : (1394159 / 200000000) ≤ -Real.log (248263361071 / 250000000000) ∧
    -Real.log (248263361071 / 250000000000) ≤ (1742699 / 250000000) := by
  have h := checkLog_sound (w := (1736638929 / 498263361071)) (n := 12)
    (lo := (1394159 / 200000000)) (hi := (1742699 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248263361071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248263361071) = 1/(248263361071 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2163 : Bounds (-1742699 / 250000000) (-1394159 / 200000000) (Real.log (248263361071 / 250000000000)) := by
  have h := reflection_log_2163_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2164_neg : (1386917 / 200000000) ≤ -Real.log (9930894031 / 10000000000) ∧
    -Real.log (9930894031 / 10000000000) ≤ (3467293 / 500000000) := by
  have h := checkLog_sound (w := (69105969 / 19930894031)) (n := 12)
    (lo := (1386917 / 200000000)) (hi := (3467293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9930894031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9930894031) = 1/(9930894031 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2164 : Bounds (-3467293 / 500000000) (-1386917 / 200000000) (Real.log (9930894031 / 10000000000)) := by
  have h := reflection_log_2164_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2165_neg : (166644581 / 1000000000) ≤ -Real.log (250000000000 / 295333580551) ∧
    -Real.log (250000000000 / 295333580551) ≤ (83322291 / 500000000) := by
  have h := checkLog_sound (w := (45333580551 / 545333580551)) (n := 12)
    (lo := (166644581 / 1000000000)) (hi := (83322291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295333580551 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295333580551 / 250000000000) = 1/(250000000000 / 295333580551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2165 : Bounds (166644581 / 1000000000) (83322291 / 500000000) (Real.log (295333580551 / 250000000000)) := by
  have h := reflection_log_2165_neg
  have he : Real.log (295333580551 / 250000000000) = -Real.log (250000000000 / 295333580551) := by
    rw [show ((295333580551 / 250000000000) : ℝ) = ((250000000000 / 295333580551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2166_neg : (33415919 / 200000000) ≤ -Real.log (250000000000 / 295462082749) ∧
    -Real.log (250000000000 / 295462082749) ≤ (41769899 / 250000000) := by
  have h := checkLog_sound (w := (45462082749 / 545462082749)) (n := 12)
    (lo := (33415919 / 200000000)) (hi := (41769899 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295462082749 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295462082749 / 250000000000) = 1/(250000000000 / 295462082749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2166 : Bounds (33415919 / 200000000) (41769899 / 250000000) (Real.log (295462082749 / 250000000000)) := by
  have h := reflection_log_2166_neg
  have he : Real.log (295462082749 / 250000000000) = -Real.log (250000000000 / 295462082749) := by
    rw [show ((295462082749 / 250000000000) : ℝ) = ((250000000000 / 295462082749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2167_neg : (334278351 / 1000000000) ≤ -Real.log (250000000000 / 349232981783) ∧
    -Real.log (250000000000 / 349232981783) ≤ (20892397 / 62500000) := by
  have h := checkLog_sound (w := (99232981783 / 599232981783)) (n := 12)
    (lo := (334278351 / 1000000000)) (hi := (20892397 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349232981783 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(349232981783 / 250000000000) = 1/(250000000000 / 349232981783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2167 : Bounds (334278351 / 1000000000) (20892397 / 62500000) (Real.log (349232981783 / 250000000000)) := by
  have h := reflection_log_2167_neg
  have he : Real.log (349232981783 / 250000000000) = -Real.log (250000000000 / 349232981783) := by
    rw [show ((349232981783 / 250000000000) : ℝ) = ((250000000000 / 349232981783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2168_neg : (167241997 / 500000000) ≤ -Real.log (10000000000 / 13972192257) ∧
    -Real.log (10000000000 / 13972192257) ≤ (66896799 / 200000000) := by
  have h := checkLog_sound (w := (3972192257 / 23972192257)) (n := 12)
    (lo := (167241997 / 500000000)) (hi := (66896799 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13972192257 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(13972192257 / 10000000000) = 1/(10000000000 / 13972192257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2168 : Bounds (167241997 / 500000000) (66896799 / 200000000) (Real.log (13972192257 / 10000000000)) := by
  have h := reflection_log_2168_neg
  have he : Real.log (13972192257 / 10000000000) = -Real.log (10000000000 / 13972192257) := by
    rw [show ((13972192257 / 10000000000) : ℝ) = ((10000000000 / 13972192257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2169_neg : (76703773 / 500000000) ≤ -Real.log (5000 / 5829) ∧
    -Real.log (5000 / 5829) ≤ (153407547 / 1000000000) := by
  have h := checkLog_sound (w := (829 / 10829)) (n := 12)
    (lo := (76703773 / 500000000)) (hi := (153407547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5829 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5829 / 5000) = 1/(5000 / 5829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2169 : Bounds (76703773 / 500000000) (153407547 / 1000000000) (Real.log (5829 / 5000)) := by
  have h := reflection_log_2169_neg
  have he : Real.log (5829 / 5000) = -Real.log (5000 / 5829) := by
    rw [show ((5829 / 5000) : ℝ) = ((5000 / 5829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2170_neg : (181282097 / 1000000000) ≤ -Real.log (4171 / 5000) ∧
    -Real.log (4171 / 5000) ≤ (90641049 / 500000000) := by
  have h := checkLog_sound (w := (829 / 9171)) (n := 12)
    (lo := (181282097 / 1000000000)) (hi := (90641049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4171) = 1/(4171 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2170 : Bounds (-90641049 / 500000000) (-181282097 / 1000000000) (Real.log (4171 / 5000)) := by
  have h := reflection_log_2170_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2171_neg : (82893 / 500000000) ≤ -Real.log (5000000 / 5000829) ∧
    -Real.log (5000000 / 5000829) ≤ (165787 / 1000000000) := by
  have h := checkLog_sound (w := (829 / 10000829)) (n := 12)
    (lo := (82893 / 500000000)) (hi := (165787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000829 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000829 / 5000000) = 1/(5000000 / 5000829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2171 : Bounds (82893 / 500000000) (165787 / 1000000000) (Real.log (5000829 / 5000000)) := by
  have h := reflection_log_2171_neg
  have he : Real.log (5000829 / 5000000) = -Real.log (5000000 / 5000829) := by
    rw [show ((5000829 / 5000000) : ℝ) = ((5000000 / 5000829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2172_neg : (165813 / 1000000000) ≤ -Real.log (4999171 / 5000000) ∧
    -Real.log (4999171 / 5000000) ≤ (82907 / 500000000) := by
  have h := checkLog_sound (w := (829 / 9999171)) (n := 12)
    (lo := (165813 / 1000000000)) (hi := (82907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999171) = 1/(4999171 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2172 : Bounds (-82907 / 500000000) (-165813 / 1000000000) (Real.log (4999171 / 5000000)) := by
  have h := reflection_log_2172_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2173_neg : (39951041 / 500000000) ≤ -Real.log (1000000 / 1083181) ∧
    -Real.log (1000000 / 1083181) ≤ (79902083 / 1000000000) := by
  have h := checkLog_sound (w := (83181 / 2083181)) (n := 12)
    (lo := (39951041 / 500000000)) (hi := (79902083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083181 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083181 / 1000000) = 1/(1000000 / 1083181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2173 : Bounds (39951041 / 500000000) (79902083 / 1000000000) (Real.log (1083181 / 1000000)) := by
  have h := reflection_log_2173_neg
  have he : Real.log (1083181 / 1000000) = -Real.log (1000000 / 1083181) := by
    rw [show ((1083181 / 1000000) : ℝ) = ((1000000 / 1083181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2174_neg : (10855651 / 125000000) ≤ -Real.log (916819 / 1000000) ∧
    -Real.log (916819 / 1000000) ≤ (86845209 / 1000000000) := by
  have h := checkLog_sound (w := (83181 / 1916819)) (n := 12)
    (lo := (10855651 / 125000000)) (hi := (86845209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916819) = 1/(916819 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2174 : Bounds (-86845209 / 1000000000) (-10855651 / 125000000) (Real.log (916819 / 1000000)) := by
  have h := reflection_log_2174_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2175_neg : (3204059 / 40000000) ≤ -Real.log (1000000 / 1083397) ∧
    -Real.log (1000000 / 1083397) ≤ (20025369 / 250000000) := by
  have h := checkLog_sound (w := (83397 / 2083397)) (n := 12)
    (lo := (3204059 / 40000000)) (hi := (20025369 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083397 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083397 / 1000000) = 1/(1000000 / 1083397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2175 : Bounds (3204059 / 40000000) (20025369 / 250000000) (Real.log (1083397 / 1000000)) := by
  have h := reflection_log_2175_neg
  have he : Real.log (1083397 / 1000000) = -Real.log (1000000 / 1083397) := by
    rw [show ((1083397 / 1000000) : ℝ) = ((1000000 / 1083397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
