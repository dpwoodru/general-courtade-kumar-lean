import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1600_neg : (84581241 / 1000000000) ≤ -Real.log (918897 / 1000000) ∧
    -Real.log (918897 / 1000000) ≤ (42290621 / 500000000) := by
  have h := checkLog_sound (w := (81103 / 1918897)) (n := 12)
    (lo := (84581241 / 1000000000)) (hi := (42290621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918897) = 1/(918897 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1600 : Bounds (-42290621 / 500000000) (-84581241 / 1000000000) (Real.log (918897 / 1000000)) := by
  have h := reflection_log_1600_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1601_neg : (78177893 / 1000000000) ≤ -Real.log (200000 / 216263) ∧
    -Real.log (200000 / 216263) ≤ (39088947 / 500000000) := by
  have h := checkLog_sound (w := (16263 / 416263)) (n := 12)
    (lo := (78177893 / 1000000000)) (hi := (39088947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216263 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216263 / 200000) = 1/(200000 / 216263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1601 : Bounds (78177893 / 1000000000) (39088947 / 500000000) (Real.log (216263 / 200000)) := by
  have h := reflection_log_1601_neg
  have he : Real.log (216263 / 200000) = -Real.log (200000 / 216263) := by
    rw [show ((216263 / 200000) : ℝ) = ((200000 / 216263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1602_neg : (84811979 / 1000000000) ≤ -Real.log (183737 / 200000) ∧
    -Real.log (183737 / 200000) ≤ (4240599 / 50000000) := by
  have h := checkLog_sound (w := (16263 / 383737)) (n := 12)
    (lo := (84811979 / 1000000000)) (hi := (4240599 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183737) = 1/(183737 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1602 : Bounds (-4240599 / 50000000) (-84811979 / 1000000000) (Real.log (183737 / 200000)) := by
  have h := reflection_log_1602_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1603_neg : (3317043 / 500000000) ≤ -Real.log (39735514831 / 40000000000) ∧
    -Real.log (39735514831 / 40000000000) ≤ (6634087 / 1000000000) := by
  have h := checkLog_sound (w := (264485169 / 79735514831)) (n := 12)
    (lo := (3317043 / 500000000)) (hi := (6634087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39735514831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39735514831) = 1/(39735514831 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1603 : Bounds (-6634087 / 1000000000) (-3317043 / 500000000) (Real.log (39735514831 / 40000000000)) := by
  have h := reflection_log_1603_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1604_neg : (25779 / 3906250) ≤ -Real.log (993422303391 / 1000000000000) ∧
    -Real.log (993422303391 / 1000000000000) ≤ (263977 / 40000000) := by
  have h := checkLog_sound (w := (6577696609 / 1993422303391)) (n := 12)
    (lo := (25779 / 3906250)) (hi := (263977 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993422303391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993422303391) = 1/(993422303391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1604 : Bounds (-263977 / 40000000) (-25779 / 3906250) (Real.log (993422303391 / 1000000000000)) := by
  have h := reflection_log_1604_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1605_neg : (162563057 / 1000000000) ≤ -Real.log (500000000000 / 588261252349) ∧
    -Real.log (500000000000 / 588261252349) ≤ (81281529 / 500000000) := by
  have h := checkLog_sound (w := (88261252349 / 1088261252349)) (n := 12)
    (lo := (162563057 / 1000000000)) (hi := (81281529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588261252349 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588261252349 / 500000000000) = 1/(500000000000 / 588261252349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1605 : Bounds (162563057 / 1000000000) (81281529 / 500000000) (Real.log (588261252349 / 500000000000)) := by
  have h := reflection_log_1605_neg
  have he : Real.log (588261252349 / 500000000000) = -Real.log (500000000000 / 588261252349) := by
    rw [show ((588261252349 / 500000000000) : ℝ) = ((500000000000 / 588261252349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1606_neg : (10186867 / 62500000) ≤ -Real.log (10000000000 / 11770247691) ∧
    -Real.log (10000000000 / 11770247691) ≤ (162989873 / 1000000000) := by
  have h := checkLog_sound (w := (1770247691 / 21770247691)) (n := 12)
    (lo := (10186867 / 62500000)) (hi := (162989873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11770247691 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11770247691 / 10000000000) = 1/(10000000000 / 11770247691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1606 : Bounds (10186867 / 62500000) (162989873 / 1000000000) (Real.log (11770247691 / 10000000000)) := by
  have h := reflection_log_1606_neg
  have he : Real.log (11770247691 / 10000000000) = -Real.log (10000000000 / 11770247691) := by
    rw [show ((11770247691 / 10000000000) : ℝ) = ((10000000000 / 11770247691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1607_neg : (32605833 / 100000000) ≤ -Real.log (500000000000 / 692748091603) ∧
    -Real.log (500000000000 / 692748091603) ≤ (326058331 / 1000000000) := by
  have h := checkLog_sound (w := (192748091603 / 1192748091603)) (n := 12)
    (lo := (32605833 / 100000000)) (hi := (326058331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((692748091603 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(692748091603 / 500000000000) = 1/(500000000000 / 692748091603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1607 : Bounds (32605833 / 100000000) (326058331 / 1000000000) (Real.log (692748091603 / 500000000000)) := by
  have h := reflection_log_1607_neg
  have he : Real.log (692748091603 / 500000000000) = -Real.log (500000000000 / 692748091603) := by
    rw [show ((692748091603 / 500000000000) : ℝ) = ((500000000000 / 692748091603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1608_neg : (20391481 / 62500000) ≤ -Real.log (4000000000 / 5543122987) ∧
    -Real.log (4000000000 / 5543122987) ≤ (326263697 / 1000000000) := by
  have h := checkLog_sound (w := (1543122987 / 9543122987)) (n := 12)
    (lo := (20391481 / 62500000)) (hi := (326263697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5543122987 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5543122987 / 4000000000) = 1/(4000000000 / 5543122987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1608 : Bounds (20391481 / 62500000) (326263697 / 1000000000) (Real.log (5543122987 / 4000000000)) := by
  have h := reflection_log_1608_neg
  have he : Real.log (5543122987 / 4000000000) = -Real.log (4000000000 / 5543122987) := by
    rw [show ((5543122987 / 4000000000) : ℝ) = ((4000000000 / 5543122987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1609_neg : (74985263 / 500000000) ≤ -Real.log (5000 / 5809) ∧
    -Real.log (5000 / 5809) ≤ (149970527 / 1000000000) := by
  have h := checkLog_sound (w := (809 / 10809)) (n := 12)
    (lo := (74985263 / 500000000)) (hi := (149970527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5809 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5809 / 5000) = 1/(5000 / 5809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1609 : Bounds (74985263 / 500000000) (149970527 / 1000000000) (Real.log (5809 / 5000)) := by
  have h := reflection_log_1609_neg
  have he : Real.log (5809 / 5000) = -Real.log (5000 / 5809) := by
    rw [show ((5809 / 5000) : ℝ) = ((5000 / 5809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1610_neg : (176498543 / 1000000000) ≤ -Real.log (4191 / 5000) ∧
    -Real.log (4191 / 5000) ≤ (11031159 / 62500000) := by
  have h := checkLog_sound (w := (809 / 9191)) (n := 12)
    (lo := (176498543 / 1000000000)) (hi := (11031159 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4191) = 1/(4191 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1610 : Bounds (-11031159 / 62500000) (-176498543 / 1000000000) (Real.log (4191 / 5000)) := by
  have h := reflection_log_1610_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1611_neg : (80893 / 500000000) ≤ -Real.log (5000000 / 5000809) ∧
    -Real.log (5000000 / 5000809) ≤ (161787 / 1000000000) := by
  have h := checkLog_sound (w := (809 / 10000809)) (n := 12)
    (lo := (80893 / 500000000)) (hi := (161787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000809 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000809 / 5000000) = 1/(5000000 / 5000809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1611 : Bounds (80893 / 500000000) (161787 / 1000000000) (Real.log (5000809 / 5000000)) := by
  have h := reflection_log_1611_neg
  have he : Real.log (5000809 / 5000000) = -Real.log (5000000 / 5000809) := by
    rw [show ((5000809 / 5000000) : ℝ) = ((5000000 / 5000809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1612_neg : (161813 / 1000000000) ≤ -Real.log (4999191 / 5000000) ∧
    -Real.log (4999191 / 5000000) ≤ (80907 / 500000000) := by
  have h := checkLog_sound (w := (809 / 9999191)) (n := 12)
    (lo := (161813 / 1000000000)) (hi := (80907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999191) = 1/(4999191 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1612 : Bounds (-80907 / 500000000) (-161813 / 1000000000) (Real.log (4999191 / 5000000)) := by
  have h := reflection_log_1612_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1613_neg : (2438377 / 31250000) ≤ -Real.log (1000000 / 1081153) ∧
    -Real.log (1000000 / 1081153) ≤ (15605613 / 200000000) := by
  have h := checkLog_sound (w := (81153 / 2081153)) (n := 12)
    (lo := (2438377 / 31250000)) (hi := (15605613 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081153 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081153 / 1000000) = 1/(1000000 / 1081153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1613 : Bounds (2438377 / 31250000) (15605613 / 200000000) (Real.log (1081153 / 1000000)) := by
  have h := reflection_log_1613_neg
  have he : Real.log (1081153 / 1000000) = -Real.log (1000000 / 1081153) := by
    rw [show ((1081153 / 1000000) : ℝ) = ((1000000 / 1081153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1614_neg : (16927131 / 200000000) ≤ -Real.log (918847 / 1000000) ∧
    -Real.log (918847 / 1000000) ≤ (10579457 / 125000000) := by
  have h := checkLog_sound (w := (81153 / 1918847)) (n := 12)
    (lo := (16927131 / 200000000)) (hi := (10579457 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918847) = 1/(918847 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1614 : Bounds (-10579457 / 125000000) (-16927131 / 200000000) (Real.log (918847 / 1000000)) := by
  have h := reflection_log_1614_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1615_neg : (2444533 / 31250000) ≤ -Real.log (500000 / 540683) ∧
    -Real.log (500000 / 540683) ≤ (78225057 / 1000000000) := by
  have h := checkLog_sound (w := (40683 / 1040683)) (n := 12)
    (lo := (2444533 / 31250000)) (hi := (78225057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((540683 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(540683 / 500000) = 1/(500000 / 540683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1615 : Bounds (2444533 / 31250000) (78225057 / 1000000000) (Real.log (540683 / 500000)) := by
  have h := reflection_log_1615_neg
  have he : Real.log (540683 / 500000) = -Real.log (500000 / 540683) := by
    rw [show ((540683 / 500000) : ℝ) = ((500000 / 540683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1616_neg : (42433747 / 500000000) ≤ -Real.log (459317 / 500000) ∧
    -Real.log (459317 / 500000) ≤ (16973499 / 200000000) := by
  have h := checkLog_sound (w := (40683 / 959317)) (n := 12)
    (lo := (42433747 / 500000000)) (hi := (16973499 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 459317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 459317) = 1/(459317 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1616 : Bounds (-16973499 / 200000000) (-42433747 / 500000000) (Real.log (459317 / 500000)) := by
  have h := reflection_log_1616_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1617_neg : (3321219 / 500000000) ≤ -Real.log (248344893511 / 250000000000) ∧
    -Real.log (248344893511 / 250000000000) ≤ (6642439 / 1000000000) := by
  have h := checkLog_sound (w := (1655106489 / 498344893511)) (n := 12)
    (lo := (3321219 / 500000000)) (hi := (6642439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248344893511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248344893511) = 1/(248344893511 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1617 : Bounds (-6642439 / 1000000000) (-3321219 / 500000000) (Real.log (248344893511 / 250000000000)) := by
  have h := reflection_log_1617_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1618_neg : (6607591 / 1000000000) ≤ -Real.log (993414190591 / 1000000000000) ∧
    -Real.log (993414190591 / 1000000000000) ≤ (825949 / 125000000) := by
  have h := checkLog_sound (w := (6585809409 / 1993414190591)) (n := 12)
    (lo := (6607591 / 1000000000)) (hi := (825949 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993414190591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993414190591) = 1/(993414190591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1618 : Bounds (-825949 / 125000000) (-6607591 / 1000000000) (Real.log (993414190591 / 1000000000000)) := by
  have h := reflection_log_1618_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1619_neg : (4066593 / 25000000) ≤ -Real.log (500000000000 / 588320471199) ∧
    -Real.log (500000000000 / 588320471199) ≤ (162663721 / 1000000000) := by
  have h := checkLog_sound (w := (88320471199 / 1088320471199)) (n := 12)
    (lo := (4066593 / 25000000)) (hi := (162663721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588320471199 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588320471199 / 500000000000) = 1/(500000000000 / 588320471199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1619 : Bounds (4066593 / 25000000) (162663721 / 1000000000) (Real.log (588320471199 / 500000000000)) := by
  have h := reflection_log_1619_neg
  have he : Real.log (588320471199 / 500000000000) = -Real.log (500000000000 / 588320471199) := by
    rw [show ((588320471199 / 500000000000) : ℝ) = ((500000000000 / 588320471199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1620_neg : (163092551 / 1000000000) ≤ -Real.log (20000000000 / 23542912629) ∧
    -Real.log (20000000000 / 23542912629) ≤ (20386569 / 125000000) := by
  have h := checkLog_sound (w := (3542912629 / 43542912629)) (n := 12)
    (lo := (163092551 / 1000000000)) (hi := (20386569 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23542912629 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23542912629 / 20000000000) = 1/(20000000000 / 23542912629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1620 : Bounds (163092551 / 1000000000) (20386569 / 125000000) (Real.log (23542912629 / 20000000000)) := by
  have h := reflection_log_1620_neg
  have he : Real.log (23542912629 / 20000000000) = -Real.log (20000000000 / 23542912629) := by
    rw [show ((23542912629 / 20000000000) : ℝ) = ((20000000000 / 23542912629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1621_neg : (20391481 / 62500000) ≤ -Real.log (250000000000 / 346445186687) ∧
    -Real.log (250000000000 / 346445186687) ≤ (326263697 / 1000000000) := by
  have h := checkLog_sound (w := (96445186687 / 596445186687)) (n := 12)
    (lo := (20391481 / 62500000)) (hi := (326263697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((346445186687 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(346445186687 / 250000000000) = 1/(250000000000 / 346445186687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1621 : Bounds (20391481 / 62500000) (326263697 / 1000000000) (Real.log (346445186687 / 250000000000)) := by
  have h := reflection_log_1621_neg
  have he : Real.log (346445186687 / 250000000000) = -Real.log (250000000000 / 346445186687) := by
    rw [show ((346445186687 / 250000000000) : ℝ) = ((250000000000 / 346445186687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1622_neg : (32646907 / 100000000) ≤ -Real.log (62500000000 / 86629086137) ∧
    -Real.log (62500000000 / 86629086137) ≤ (326469071 / 1000000000) := by
  have h := checkLog_sound (w := (24129086137 / 149129086137)) (n := 12)
    (lo := (32646907 / 100000000)) (hi := (326469071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86629086137 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86629086137 / 62500000000) = 1/(62500000000 / 86629086137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1622 : Bounds (32646907 / 100000000) (326469071 / 1000000000) (Real.log (86629086137 / 62500000000)) := by
  have h := reflection_log_1622_neg
  have he : Real.log (86629086137 / 62500000000) = -Real.log (62500000000 / 86629086137) := by
    rw [show ((86629086137 / 62500000000) : ℝ) = ((62500000000 / 86629086137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1623_neg : (37514149 / 250000000) ≤ -Real.log (10000 / 11619) ∧
    -Real.log (10000 / 11619) ≤ (150056597 / 1000000000) := by
  have h := checkLog_sound (w := (1619 / 21619)) (n := 12)
    (lo := (37514149 / 250000000)) (hi := (150056597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11619 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11619 / 10000) = 1/(10000 / 11619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1623 : Bounds (37514149 / 250000000) (150056597 / 1000000000) (Real.log (11619 / 10000)) := by
  have h := reflection_log_1623_neg
  have he : Real.log (11619 / 10000) = -Real.log (10000 / 11619) := by
    rw [show ((11619 / 10000) : ℝ) = ((10000 / 11619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1624_neg : (176617853 / 1000000000) ≤ -Real.log (8381 / 10000) ∧
    -Real.log (8381 / 10000) ≤ (88308927 / 500000000) := by
  have h := checkLog_sound (w := (1619 / 18381)) (n := 12)
    (lo := (176617853 / 1000000000)) (hi := (88308927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8381) = 1/(8381 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1624 : Bounds (-88308927 / 500000000) (-176617853 / 1000000000) (Real.log (8381 / 10000)) := by
  have h := reflection_log_1624_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1625_neg : (80943 / 500000000) ≤ -Real.log (10000000 / 10001619) ∧
    -Real.log (10000000 / 10001619) ≤ (161887 / 1000000000) := by
  have h := checkLog_sound (w := (1619 / 20001619)) (n := 12)
    (lo := (80943 / 500000000)) (hi := (161887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001619 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001619 / 10000000) = 1/(10000000 / 10001619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1625 : Bounds (80943 / 500000000) (161887 / 1000000000) (Real.log (10001619 / 10000000)) := by
  have h := reflection_log_1625_neg
  have he : Real.log (10001619 / 10000000) = -Real.log (10000000 / 10001619) := by
    rw [show ((10001619 / 10000000) : ℝ) = ((10000000 / 10001619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1626_neg : (161913 / 1000000000) ≤ -Real.log (9998381 / 10000000) ∧
    -Real.log (9998381 / 10000000) ≤ (80957 / 500000000) := by
  have h := checkLog_sound (w := (1619 / 19998381)) (n := 12)
    (lo := (161913 / 1000000000)) (hi := (80957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998381) = 1/(9998381 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1626 : Bounds (-80957 / 500000000) (-161913 / 1000000000) (Real.log (9998381 / 10000000)) := by
  have h := reflection_log_1626_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1627_neg : (15615047 / 200000000) ≤ -Real.log (250000 / 270301) ∧
    -Real.log (250000 / 270301) ≤ (19518809 / 250000000) := by
  have h := checkLog_sound (w := (20301 / 520301)) (n := 12)
    (lo := (15615047 / 200000000)) (hi := (19518809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270301 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270301 / 250000) = 1/(250000 / 270301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1627 : Bounds (15615047 / 200000000) (19518809 / 250000000) (Real.log (270301 / 250000)) := by
  have h := reflection_log_1627_neg
  have he : Real.log (270301 / 250000) = -Real.log (250000 / 270301) := by
    rw [show ((270301 / 250000) : ℝ) = ((250000 / 270301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1628_neg : (84691161 / 1000000000) ≤ -Real.log (229699 / 250000) ∧
    -Real.log (229699 / 250000) ≤ (42345581 / 500000000) := by
  have h := checkLog_sound (w := (20301 / 479699)) (n := 12)
    (lo := (84691161 / 1000000000)) (hi := (42345581 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229699) = 1/(229699 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1628 : Bounds (-42345581 / 500000000) (-84691161 / 1000000000) (Real.log (229699 / 250000)) := by
  have h := reflection_log_1628_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1629_neg : (39136109 / 500000000) ≤ -Real.log (1000000 / 1081417) ∧
    -Real.log (1000000 / 1081417) ≤ (78272219 / 1000000000) := by
  have h := checkLog_sound (w := (81417 / 2081417)) (n := 12)
    (lo := (39136109 / 500000000)) (hi := (78272219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081417 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081417 / 1000000) = 1/(1000000 / 1081417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1629 : Bounds (39136109 / 500000000) (78272219 / 1000000000) (Real.log (1081417 / 1000000)) := by
  have h := reflection_log_1629_neg
  have he : Real.log (1081417 / 1000000) = -Real.log (1000000 / 1081417) := by
    rw [show ((1081417 / 1000000) : ℝ) = ((1000000 / 1081417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1630_neg : (84923013 / 1000000000) ≤ -Real.log (918583 / 1000000) ∧
    -Real.log (918583 / 1000000) ≤ (42461507 / 500000000) := by
  have h := checkLog_sound (w := (81417 / 1918583)) (n := 12)
    (lo := (84923013 / 1000000000)) (hi := (42461507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918583) = 1/(918583 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1630 : Bounds (-42461507 / 500000000) (-84923013 / 1000000000) (Real.log (918583 / 1000000)) := by
  have h := reflection_log_1630_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1631_neg : (1330159 / 200000000) ≤ -Real.log (993371272111 / 1000000000000) ∧
    -Real.log (993371272111 / 1000000000000) ≤ (1662699 / 250000000) := by
  have h := checkLog_sound (w := (6628727889 / 1993371272111)) (n := 12)
    (lo := (1330159 / 200000000)) (hi := (1662699 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993371272111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993371272111) = 1/(993371272111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1631 : Bounds (-1662699 / 250000000) (-1330159 / 200000000) (Real.log (993371272111 / 1000000000000)) := by
  have h := reflection_log_1631_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1632_neg : (3307963 / 500000000) ≤ -Real.log (62087869399 / 62500000000) ∧
    -Real.log (62087869399 / 62500000000) ≤ (6615927 / 1000000000) := by
  have h := checkLog_sound (w := (412130601 / 124587869399)) (n := 12)
    (lo := (3307963 / 500000000)) (hi := (6615927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62087869399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62087869399) = 1/(62087869399 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1632 : Bounds (-6615927 / 1000000000) (-3307963 / 500000000) (Real.log (62087869399 / 62500000000)) := by
  have h := reflection_log_1632_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1633_neg : (40691599 / 250000000) ≤ -Real.log (250000000000 / 294190440533) ∧
    -Real.log (250000000000 / 294190440533) ≤ (162766397 / 1000000000) := by
  have h := checkLog_sound (w := (44190440533 / 544190440533)) (n := 12)
    (lo := (40691599 / 250000000)) (hi := (162766397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294190440533 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294190440533 / 250000000000) = 1/(250000000000 / 294190440533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1633 : Bounds (40691599 / 250000000) (162766397 / 1000000000) (Real.log (294190440533 / 250000000000)) := by
  have h := reflection_log_1633_neg
  have he : Real.log (294190440533 / 250000000000) = -Real.log (250000000000 / 294190440533) := by
    rw [show ((294190440533 / 250000000000) : ℝ) = ((250000000000 / 294190440533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1634_neg : (163195231 / 1000000000) ≤ -Real.log (50000000000 / 58863325361) ∧
    -Real.log (50000000000 / 58863325361) ≤ (5099851 / 31250000) := by
  have h := checkLog_sound (w := (8863325361 / 108863325361)) (n := 12)
    (lo := (163195231 / 1000000000)) (hi := (5099851 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58863325361 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58863325361 / 50000000000) = 1/(50000000000 / 58863325361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1634 : Bounds (163195231 / 1000000000) (5099851 / 31250000) (Real.log (58863325361 / 50000000000)) := by
  have h := reflection_log_1634_neg
  have he : Real.log (58863325361 / 50000000000) = -Real.log (50000000000 / 58863325361) := by
    rw [show ((58863325361 / 50000000000) : ℝ) = ((50000000000 / 58863325361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1635_neg : (32646907 / 100000000) ≤ -Real.log (100000000000 / 138606537819) ∧
    -Real.log (100000000000 / 138606537819) ≤ (326469071 / 1000000000) := by
  have h := checkLog_sound (w := (38606537819 / 238606537819)) (n := 12)
    (lo := (32646907 / 100000000)) (hi := (326469071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138606537819 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(138606537819 / 100000000000) = 1/(100000000000 / 138606537819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1635 : Bounds (32646907 / 100000000) (326469071 / 1000000000) (Real.log (138606537819 / 100000000000)) := by
  have h := reflection_log_1635_neg
  have he : Real.log (138606537819 / 100000000000) = -Real.log (100000000000 / 138606537819) := by
    rw [show ((138606537819 / 100000000000) : ℝ) = ((100000000000 / 138606537819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1636_neg : (6533489 / 20000000) ≤ -Real.log (500000000000 / 693175038779) ∧
    -Real.log (500000000000 / 693175038779) ≤ (326674451 / 1000000000) := by
  have h := checkLog_sound (w := (193175038779 / 1193175038779)) (n := 12)
    (lo := (6533489 / 20000000)) (hi := (326674451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693175038779 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693175038779 / 500000000000) = 1/(500000000000 / 693175038779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1636 : Bounds (6533489 / 20000000) (326674451 / 1000000000) (Real.log (693175038779 / 500000000000)) := by
  have h := reflection_log_1636_neg
  have he : Real.log (693175038779 / 500000000000) = -Real.log (500000000000 / 693175038779) := by
    rw [show ((693175038779 / 500000000000) : ℝ) = ((500000000000 / 693175038779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1637_neg : (75071329 / 500000000) ≤ -Real.log (500 / 581) ∧
    -Real.log (500 / 581) ≤ (150142659 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 1081)) (n := 12)
    (lo := (75071329 / 500000000)) (hi := (150142659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581 / 500) = 1/(500 / 581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1637 : Bounds (75071329 / 500000000) (150142659 / 1000000000) (Real.log (581 / 500)) := by
  have h := reflection_log_1637_neg
  have he : Real.log (581 / 500) = -Real.log (500 / 581) := by
    rw [show ((581 / 500) : ℝ) = ((500 / 581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1638_neg : (88368589 / 500000000) ≤ -Real.log (419 / 500) ∧
    -Real.log (419 / 500) ≤ (176737179 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 919)) (n := 12)
    (lo := (88368589 / 500000000)) (hi := (176737179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 419) = 1/(419 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1638 : Bounds (-176737179 / 1000000000) (-88368589 / 500000000) (Real.log (419 / 500)) := by
  have h := reflection_log_1638_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1639_neg : (80993 / 500000000) ≤ -Real.log (500000 / 500081) ∧
    -Real.log (500000 / 500081) ≤ (161987 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 1000081)) (n := 12)
    (lo := (80993 / 500000000)) (hi := (161987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500081 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500081 / 500000) = 1/(500000 / 500081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1639 : Bounds (80993 / 500000000) (161987 / 1000000000) (Real.log (500081 / 500000)) := by
  have h := reflection_log_1639_neg
  have he : Real.log (500081 / 500000) = -Real.log (500000 / 500081) := by
    rw [show ((500081 / 500000) : ℝ) = ((500000 / 500081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1640_neg : (162013 / 1000000000) ≤ -Real.log (499919 / 500000) ∧
    -Real.log (499919 / 500000) ≤ (81007 / 500000000) := by
  have h := checkLog_sound (w := (81 / 999919)) (n := 12)
    (lo := (162013 / 1000000000)) (hi := (81007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499919) = 1/(499919 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1640 : Bounds (-81007 / 500000000) (-162013 / 1000000000) (Real.log (499919 / 500000)) := by
  have h := reflection_log_1640_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1641_neg : (78122403 / 1000000000) ≤ -Real.log (200000 / 216251) ∧
    -Real.log (200000 / 216251) ≤ (19530601 / 250000000) := by
  have h := checkLog_sound (w := (16251 / 416251)) (n := 12)
    (lo := (78122403 / 1000000000)) (hi := (19530601 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216251 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216251 / 200000) = 1/(200000 / 216251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1641 : Bounds (78122403 / 1000000000) (19530601 / 250000000) (Real.log (216251 / 200000)) := by
  have h := reflection_log_1641_neg
  have he : Real.log (216251 / 200000) = -Real.log (200000 / 216251) := by
    rw [show ((216251 / 200000) : ℝ) = ((200000 / 216251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1642_neg : (8474667 / 100000000) ≤ -Real.log (183749 / 200000) ∧
    -Real.log (183749 / 200000) ≤ (84746671 / 1000000000) := by
  have h := checkLog_sound (w := (16251 / 383749)) (n := 12)
    (lo := (8474667 / 100000000)) (hi := (84746671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183749) = 1/(183749 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1642 : Bounds (-84746671 / 1000000000) (-8474667 / 100000000) (Real.log (183749 / 200000)) := by
  have h := reflection_log_1642_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1643_neg : (19579613 / 250000000) ≤ -Real.log (1000000 / 1081467) ∧
    -Real.log (1000000 / 1081467) ≤ (78318453 / 1000000000) := by
  have h := checkLog_sound (w := (81467 / 2081467)) (n := 12)
    (lo := (19579613 / 250000000)) (hi := (78318453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081467 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081467 / 1000000) = 1/(1000000 / 1081467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1643 : Bounds (19579613 / 250000000) (78318453 / 1000000000) (Real.log (1081467 / 1000000)) := by
  have h := reflection_log_1643_neg
  have he : Real.log (1081467 / 1000000) = -Real.log (1000000 / 1081467) := by
    rw [show ((1081467 / 1000000) : ℝ) = ((1000000 / 1081467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1644_neg : (42488723 / 500000000) ≤ -Real.log (918533 / 1000000) ∧
    -Real.log (918533 / 1000000) ≤ (84977447 / 1000000000) := by
  have h := checkLog_sound (w := (81467 / 1918533)) (n := 12)
    (lo := (42488723 / 500000000)) (hi := (84977447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918533) = 1/(918533 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1644 : Bounds (-84977447 / 1000000000) (-42488723 / 500000000) (Real.log (918533 / 1000000)) := by
  have h := reflection_log_1644_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1645_neg : (3329497 / 500000000) ≤ -Real.log (993363127911 / 1000000000000) ∧
    -Real.log (993363127911 / 1000000000000) ≤ (1331799 / 200000000) := by
  have h := checkLog_sound (w := (6636872089 / 1993363127911)) (n := 12)
    (lo := (3329497 / 500000000)) (hi := (1331799 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993363127911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993363127911) = 1/(993363127911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1645 : Bounds (-1331799 / 200000000) (-3329497 / 500000000) (Real.log (993363127911 / 1000000000000)) := by
  have h := reflection_log_1645_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1646_neg : (6624267 / 1000000000) ≤ -Real.log (39735904999 / 40000000000) ∧
    -Real.log (39735904999 / 40000000000) ≤ (1656067 / 250000000) := by
  have h := checkLog_sound (w := (264095001 / 79735904999)) (n := 12)
    (lo := (6624267 / 1000000000)) (hi := (1656067 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39735904999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39735904999) = 1/(39735904999 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1646 : Bounds (-1656067 / 250000000) (-6624267 / 1000000000) (Real.log (39735904999 / 40000000000)) := by
  have h := reflection_log_1646_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1647_neg : (81434537 / 500000000) ≤ -Real.log (500000000000 / 588441297639) ∧
    -Real.log (500000000000 / 588441297639) ≤ (6514763 / 40000000) := by
  have h := checkLog_sound (w := (88441297639 / 1088441297639)) (n := 12)
    (lo := (81434537 / 500000000)) (hi := (6514763 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588441297639 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588441297639 / 500000000000) = 1/(500000000000 / 588441297639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1647 : Bounds (81434537 / 500000000) (6514763 / 40000000) (Real.log (588441297639 / 500000000000)) := by
  have h := reflection_log_1647_neg
  have he : Real.log (588441297639 / 500000000000) = -Real.log (500000000000 / 588441297639) := by
    rw [show ((588441297639 / 500000000000) : ℝ) = ((500000000000 / 588441297639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1648_neg : (163295899 / 1000000000) ≤ -Real.log (500000000000 / 588692512953) ∧
    -Real.log (500000000000 / 588692512953) ≤ (1632959 / 10000000) := by
  have h := checkLog_sound (w := (88692512953 / 1088692512953)) (n := 12)
    (lo := (163295899 / 1000000000)) (hi := (1632959 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588692512953 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588692512953 / 500000000000) = 1/(500000000000 / 588692512953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1648 : Bounds (163295899 / 1000000000) (1632959 / 10000000) (Real.log (588692512953 / 500000000000)) := by
  have h := reflection_log_1648_neg
  have he : Real.log (588692512953 / 500000000000) = -Real.log (500000000000 / 588692512953) := by
    rw [show ((588692512953 / 500000000000) : ℝ) = ((500000000000 / 588692512953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1649_neg : (6533489 / 20000000) ≤ -Real.log (250000000000 / 346587519389) ∧
    -Real.log (250000000000 / 346587519389) ≤ (326674451 / 1000000000) := by
  have h := checkLog_sound (w := (96587519389 / 596587519389)) (n := 12)
    (lo := (6533489 / 20000000)) (hi := (326674451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((346587519389 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(346587519389 / 250000000000) = 1/(250000000000 / 346587519389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1649 : Bounds (6533489 / 20000000) (326674451 / 1000000000) (Real.log (346587519389 / 250000000000)) := by
  have h := reflection_log_1649_neg
  have he : Real.log (346587519389 / 250000000000) = -Real.log (250000000000 / 346587519389) := by
    rw [show ((346587519389 / 250000000000) : ℝ) = ((250000000000 / 346587519389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1650_neg : (81719959 / 250000000) ≤ -Real.log (100000000000 / 138663484487) ∧
    -Real.log (100000000000 / 138663484487) ≤ (326879837 / 1000000000) := by
  have h := checkLog_sound (w := (38663484487 / 238663484487)) (n := 12)
    (lo := (81719959 / 250000000)) (hi := (326879837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138663484487 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(138663484487 / 100000000000) = 1/(100000000000 / 138663484487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1650 : Bounds (81719959 / 250000000) (326879837 / 1000000000) (Real.log (138663484487 / 100000000000)) := by
  have h := reflection_log_1650_neg
  have he : Real.log (138663484487 / 100000000000) = -Real.log (100000000000 / 138663484487) := by
    rw [show ((138663484487 / 100000000000) : ℝ) = ((100000000000 / 138663484487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1651_neg : (150228713 / 1000000000) ≤ -Real.log (10000 / 11621) ∧
    -Real.log (10000 / 11621) ≤ (75114357 / 500000000) := by
  have h := checkLog_sound (w := (1621 / 21621)) (n := 12)
    (lo := (150228713 / 1000000000)) (hi := (75114357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11621 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11621 / 10000) = 1/(10000 / 11621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1651 : Bounds (150228713 / 1000000000) (75114357 / 500000000) (Real.log (11621 / 10000)) := by
  have h := reflection_log_1651_neg
  have he : Real.log (11621 / 10000) = -Real.log (10000 / 11621) := by
    rw [show ((11621 / 10000) : ℝ) = ((10000 / 11621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1652_neg : (176856517 / 1000000000) ≤ -Real.log (8379 / 10000) ∧
    -Real.log (8379 / 10000) ≤ (88428259 / 500000000) := by
  have h := checkLog_sound (w := (1621 / 18379)) (n := 12)
    (lo := (176856517 / 1000000000)) (hi := (88428259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8379) = 1/(8379 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1652 : Bounds (-88428259 / 500000000) (-176856517 / 1000000000) (Real.log (8379 / 10000)) := by
  have h := reflection_log_1652_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1653_neg : (81043 / 500000000) ≤ -Real.log (10000000 / 10001621) ∧
    -Real.log (10000000 / 10001621) ≤ (162087 / 1000000000) := by
  have h := checkLog_sound (w := (1621 / 20001621)) (n := 12)
    (lo := (81043 / 500000000)) (hi := (162087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001621 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001621 / 10000000) = 1/(10000000 / 10001621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1653 : Bounds (81043 / 500000000) (162087 / 1000000000) (Real.log (10001621 / 10000000)) := by
  have h := reflection_log_1653_neg
  have he : Real.log (10001621 / 10000000) = -Real.log (10000000 / 10001621) := by
    rw [show ((10001621 / 10000000) : ℝ) = ((10000000 / 10001621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1654_neg : (162113 / 1000000000) ≤ -Real.log (9998379 / 10000000) ∧
    -Real.log (9998379 / 10000000) ≤ (81057 / 500000000) := by
  have h := checkLog_sound (w := (1621 / 19998379)) (n := 12)
    (lo := (162113 / 1000000000)) (hi := (81057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998379) = 1/(9998379 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1654 : Bounds (-81057 / 500000000) (-162113 / 1000000000) (Real.log (9998379 / 10000000)) := by
  have h := reflection_log_1654_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1655_neg : (15633729 / 200000000) ≤ -Real.log (200000 / 216261) ∧
    -Real.log (200000 / 216261) ≤ (39084323 / 500000000) := by
  have h := checkLog_sound (w := (16261 / 416261)) (n := 12)
    (lo := (15633729 / 200000000)) (hi := (39084323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216261 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216261 / 200000) = 1/(200000 / 216261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1655 : Bounds (15633729 / 200000000) (39084323 / 500000000) (Real.log (216261 / 200000)) := by
  have h := reflection_log_1655_neg
  have he : Real.log (216261 / 200000) = -Real.log (200000 / 216261) := by
    rw [show ((216261 / 200000) : ℝ) = ((200000 / 216261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1656_neg : (42400547 / 500000000) ≤ -Real.log (183739 / 200000) ∧
    -Real.log (183739 / 200000) ≤ (16960219 / 200000000) := by
  have h := checkLog_sound (w := (16261 / 383739)) (n := 12)
    (lo := (42400547 / 500000000)) (hi := (16960219 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183739) = 1/(183739 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1656 : Bounds (-16960219 / 200000000) (-42400547 / 500000000) (Real.log (183739 / 200000)) := by
  have h := reflection_log_1656_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1657_neg : (78365609 / 1000000000) ≤ -Real.log (500000 / 540759) ∧
    -Real.log (500000 / 540759) ≤ (7836561 / 100000000) := by
  have h := checkLog_sound (w := (40759 / 1040759)) (n := 12)
    (lo := (78365609 / 1000000000)) (hi := (7836561 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((540759 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(540759 / 500000) = 1/(500000 / 540759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1657 : Bounds (78365609 / 1000000000) (7836561 / 100000000) (Real.log (540759 / 500000)) := by
  have h := reflection_log_1657_neg
  have he : Real.log (540759 / 500000) = -Real.log (500000 / 540759) := by
    rw [show ((540759 / 500000) : ℝ) = ((500000 / 540759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1658_neg : (85032971 / 1000000000) ≤ -Real.log (459241 / 500000) ∧
    -Real.log (459241 / 500000) ≤ (21258243 / 250000000) := by
  have h := checkLog_sound (w := (40759 / 959241)) (n := 12)
    (lo := (85032971 / 1000000000)) (hi := (21258243 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 459241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 459241) = 1/(459241 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1658 : Bounds (-21258243 / 250000000) (-85032971 / 1000000000) (Real.log (459241 / 500000)) := by
  have h := reflection_log_1658_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1659_neg : (6667361 / 1000000000) ≤ -Real.log (248338703919 / 250000000000) ∧
    -Real.log (248338703919 / 250000000000) ≤ (3333681 / 500000000) := by
  have h := checkLog_sound (w := (1661296081 / 498338703919)) (n := 12)
    (lo := (6667361 / 1000000000)) (hi := (3333681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248338703919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248338703919) = 1/(248338703919 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1659 : Bounds (-3333681 / 500000000) (-6667361 / 1000000000) (Real.log (248338703919 / 250000000000)) := by
  have h := reflection_log_1659_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1660_neg : (6632449 / 1000000000) ≤ -Real.log (39735579879 / 40000000000) ∧
    -Real.log (39735579879 / 40000000000) ≤ (132649 / 20000000) := by
  have h := checkLog_sound (w := (264420121 / 79735579879)) (n := 12)
    (lo := (6632449 / 1000000000)) (hi := (132649 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39735579879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39735579879) = 1/(39735579879 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1660 : Bounds (-132649 / 20000000) (-6632449 / 1000000000) (Real.log (39735579879 / 40000000000)) := by
  have h := reflection_log_1660_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1661_neg : (162969739 / 1000000000) ≤ -Real.log (250000000000 / 294250268043) ∧
    -Real.log (250000000000 / 294250268043) ≤ (8148487 / 50000000) := by
  have h := checkLog_sound (w := (44250268043 / 544250268043)) (n := 12)
    (lo := (162969739 / 1000000000)) (hi := (8148487 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294250268043 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294250268043 / 250000000000) = 1/(250000000000 / 294250268043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1661 : Bounds (162969739 / 1000000000) (8148487 / 50000000) (Real.log (294250268043 / 250000000000)) := by
  have h := reflection_log_1661_neg
  have he : Real.log (294250268043 / 250000000000) = -Real.log (250000000000 / 294250268043) := by
    rw [show ((294250268043 / 250000000000) : ℝ) = ((250000000000 / 294250268043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1662_neg : (163398581 / 1000000000) ≤ -Real.log (50000000000 / 58875296413) ∧
    -Real.log (50000000000 / 58875296413) ≤ (81699291 / 500000000) := by
  have h := checkLog_sound (w := (8875296413 / 108875296413)) (n := 12)
    (lo := (163398581 / 1000000000)) (hi := (81699291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58875296413 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58875296413 / 50000000000) = 1/(50000000000 / 58875296413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1662 : Bounds (163398581 / 1000000000) (81699291 / 500000000) (Real.log (58875296413 / 50000000000)) := by
  have h := reflection_log_1662_neg
  have he : Real.log (58875296413 / 50000000000) = -Real.log (50000000000 / 58875296413) := by
    rw [show ((58875296413 / 50000000000) : ℝ) = ((50000000000 / 58875296413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1663_neg : (81719959 / 250000000) ≤ -Real.log (250000000000 / 346658711217) ∧
    -Real.log (250000000000 / 346658711217) ≤ (326879837 / 1000000000) := by
  have h := checkLog_sound (w := (96658711217 / 596658711217)) (n := 12)
    (lo := (81719959 / 250000000)) (hi := (326879837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((346658711217 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(346658711217 / 250000000000) = 1/(250000000000 / 346658711217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1663 : Bounds (81719959 / 250000000) (326879837 / 1000000000) (Real.log (346658711217 / 250000000000)) := by
  have h := reflection_log_1663_neg
  have he : Real.log (346658711217 / 250000000000) = -Real.log (250000000000 / 346658711217) := by
    rw [show ((346658711217 / 250000000000) : ℝ) = ((250000000000 / 346658711217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
