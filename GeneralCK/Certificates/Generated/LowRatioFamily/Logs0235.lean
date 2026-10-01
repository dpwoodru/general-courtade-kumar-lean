import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_15040_neg : (490804111 / 500000000) ≤ -Real.log (93677 / 250000) ∧
    -Real.log (93677 / 250000) ≤ (30675257 / 31250000) := by
  have h := checkLog_sound (w := (31323 / 218677)) (n := 12)
    (lo := (144230521 / 500000000)) (hi := (288461043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 93677) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 93677) = 1/(93677 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15040 : Bounds (-30675257 / 31250000) (-490804111 / 500000000) (Real.log (93677 / 250000)) := by
  have h := reflection_log_15040_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15041_neg : (243437133 / 500000000) ≤ -Real.log (500000 / 813611) ∧
    -Real.log (500000 / 813611) ≤ (486874267 / 1000000000) := by
  have h := checkLog_sound (w := (313611 / 1313611)) (n := 12)
    (lo := (243437133 / 500000000)) (hi := (486874267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((813611 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(813611 / 500000) = 1/(500000 / 813611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15041 : Bounds (243437133 / 500000000) (486874267 / 1000000000) (Real.log (813611 / 500000)) := by
  have h := reflection_log_15041_neg
  have he : Real.log (813611 / 500000) = -Real.log (500000 / 813611) := by
    rw [show ((813611 / 500000) : ℝ) = ((500000 / 813611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15042_neg : (98677221 / 100000000) ≤ -Real.log (186389 / 500000) ∧
    -Real.log (186389 / 500000) ≤ (246693053 / 250000000) := by
  have h := checkLog_sound (w := (63611 / 436389)) (n := 12)
    (lo := (29362503 / 100000000)) (hi := (293625031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 186389) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 186389) = 1/(186389 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15042 : Bounds (-246693053 / 250000000) (-98677221 / 100000000) (Real.log (186389 / 500000)) := by
  have h := reflection_log_15042_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15043_neg : (62487243 / 125000000) ≤ -Real.log (151648140679 / 250000000000) ∧
    -Real.log (151648140679 / 250000000000) ≤ (99979589 / 200000000) := by
  have h := checkLog_sound (w := (98351859321 / 401648140679)) (n := 12)
    (lo := (62487243 / 125000000)) (hi := (99979589 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 151648140679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 151648140679) = 1/(151648140679 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15043 : Bounds (-99979589 / 200000000) (-62487243 / 125000000) (Real.log (151648140679 / 250000000000)) := by
  have h := reflection_log_15043_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15044_neg : (495920731 / 1000000000) ≤ -Real.log (38063119671 / 62500000000) ∧
    -Real.log (38063119671 / 62500000000) ≤ (123980183 / 250000000) := by
  have h := checkLog_sound (w := (24436880329 / 100563119671)) (n := 12)
    (lo := (495920731 / 1000000000)) (hi := (123980183 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 38063119671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 38063119671) = 1/(38063119671 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15044 : Bounds (-123980183 / 250000000) (-495920731 / 1000000000) (Real.log (38063119671 / 62500000000)) := by
  have h := reflection_log_15044_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15045_neg : (1467295713 / 1000000000) ≤ -Real.log (500000000000 / 2168744729229) ∧
    -Real.log (500000000000 / 2168744729229) ≤ (366823929 / 250000000) := by
  have h := checkLog_sound (w := (168744729229 / 4168744729229)) (n := 12)
    (lo := (81001353 / 1000000000)) (hi := (40500677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2168744729229 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2168744729229 / 2000000000000) = 1/(500000000000 / 2168744729229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15045 : Bounds (1467295713 / 1000000000) (366823929 / 250000000) (Real.log (2168744729229 / 500000000000)) := by
  have h := reflection_log_15045_neg
  have he : Real.log (2168744729229 / 500000000000) = -Real.log (500000000000 / 2168744729229) := by
    rw [show ((2168744729229 / 500000000000) : ℝ) = ((500000000000 / 2168744729229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15046_neg : (368411619 / 250000000) ≤ -Real.log (500000000000 / 2182561739159) ∧
    -Real.log (500000000000 / 2182561739159) ≤ (1473646479 / 1000000000) := by
  have h := checkLog_sound (w := (182561739159 / 4182561739159)) (n := 12)
    (lo := (21838029 / 250000000)) (hi := (87352117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2182561739159 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2182561739159 / 2000000000000) = 1/(500000000000 / 2182561739159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15046 : Bounds (368411619 / 250000000) (1473646479 / 1000000000) (Real.log (2182561739159 / 500000000000)) := by
  have h := reflection_log_15046_neg
  have he : Real.log (2182561739159 / 500000000000) = -Real.log (500000000000 / 2182561739159) := by
    rw [show ((2182561739159 / 500000000000) : ℝ) = ((500000000000 / 2182561739159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15047_neg : (899759811 / 200000000) ≤ -Real.log (100000000000 / 8990909090909) ∧
    -Real.log (100000000000 / 8990909090909) ≤ (2249399531 / 500000000) := by
  have h := checkLog_sound (w := (2590909090909 / 15390909090909)) (n := 12)
    (lo := (13596639 / 40000000)) (hi := (42489497 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8990909090909 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(8990909090909 / 6400000000000) = 1/(100000000000 / 8990909090909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15047 : Bounds (899759811 / 200000000) (2249399531 / 500000000) (Real.log (8990909090909 / 100000000000)) := by
  have h := reflection_log_15047_neg
  have he : Real.log (8990909090909 / 100000000000) = -Real.log (100000000000 / 8990909090909) := by
    rw [show ((8990909090909 / 100000000000) : ℝ) = ((100000000000 / 8990909090909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15048_neg : (568228063 / 125000000) ≤ -Real.log (62500000000 / 5889880952381) ∧
    -Real.log (62500000000 / 5889880952381) ≤ (4545824511 / 1000000000) := by
  have h := checkLog_sound (w := (1889880952381 / 9889880952381)) (n := 12)
    (lo := (24183839 / 62500000)) (hi := (15477657 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5889880952381 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5889880952381 / 4000000000000) = 1/(62500000000 / 5889880952381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15048 : Bounds (568228063 / 125000000) (4545824511 / 1000000000) (Real.log (5889880952381 / 62500000000)) := by
  have h := reflection_log_15048_neg
  have he : Real.log (5889880952381 / 62500000000) = -Real.log (62500000000 / 5889880952381) := by
    rw [show ((5889880952381 / 62500000000) : ℝ) = ((62500000000 / 5889880952381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15049_neg : (170774211 / 250000000) ≤ -Real.log (50 / 99) ∧
    -Real.log (50 / 99) ≤ (136619369 / 200000000) := by
  have h := checkLog_sound (w := (49 / 149)) (n := 12)
    (lo := (170774211 / 250000000)) (hi := (136619369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99 / 50) = 1/(50 / 99) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15049 : Bounds (170774211 / 250000000) (136619369 / 200000000) (Real.log (99 / 50)) := by
  have h := reflection_log_15049_neg
  have he : Real.log (99 / 50) = -Real.log (50 / 99) := by
    rw [show ((99 / 50) : ℝ) = ((50 / 99) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15050_neg : (1956011501 / 500000000) ≤ -Real.log (1 / 50) ∧
    -Real.log (1 / 50) ≤ (122250719 / 31250000) := by
  have h := checkLog_sound (w := (9 / 41)) (n := 12)
    (lo := (223143551 / 500000000)) (hi := (446287103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 16) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(25 / 16) = 1/(1 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15050 : Bounds (-122250719 / 31250000) (-1956011501 / 500000000) (Real.log (1 / 50)) := by
  have h := reflection_log_15050_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15051_neg : (3061 / 3125000) ≤ -Real.log (50000 / 50049) ∧
    -Real.log (50000 / 50049) ≤ (979521 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 100049)) (n := 12)
    (lo := (3061 / 3125000)) (hi := (979521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50049 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50049 / 50000) = 1/(50000 / 50049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15051 : Bounds (3061 / 3125000) (979521 / 1000000000) (Real.log (50049 / 50000)) := by
  have h := reflection_log_15051_neg
  have he : Real.log (50049 / 50000) = -Real.log (50000 / 50049) := by
    rw [show ((50049 / 50000) : ℝ) = ((50000 / 50049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15052_neg : (383 / 390625) ≤ -Real.log (49951 / 50000) ∧
    -Real.log (49951 / 50000) ≤ (980481 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 99951)) (n := 12)
    (lo := (383 / 390625)) (hi := (980481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 49951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 49951) = 1/(49951 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15052 : Bounds (-980481 / 1000000000) (-383 / 390625) (Real.log (49951 / 50000)) := by
  have h := reflection_log_15052_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15053_neg : (97296053 / 200000000) ≤ -Real.log (1000000 / 1626581) ∧
    -Real.log (1000000 / 1626581) ≤ (243240133 / 500000000) := by
  have h := checkLog_sound (w := (626581 / 2626581)) (n := 12)
    (lo := (97296053 / 200000000)) (hi := (243240133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1626581 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1626581 / 1000000) = 1/(1000000 / 1626581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15053 : Bounds (97296053 / 200000000) (243240133 / 500000000) (Real.log (1626581 / 1000000)) := by
  have h := reflection_log_15053_neg
  have he : Real.log (1626581 / 1000000) = -Real.log (1000000 / 1626581) := by
    rw [show ((1626581 / 1000000) : ℝ) = ((1000000 / 1626581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15054_neg : (246263541 / 250000000) ≤ -Real.log (373419 / 1000000) ∧
    -Real.log (373419 / 1000000) ≤ (492527083 / 500000000) := by
  have h := checkLog_sound (w := (126581 / 873419)) (n := 12)
    (lo := (36488373 / 125000000)) (hi := (58381397 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 373419) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 373419) = 1/(373419 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15054 : Bounds (-492527083 / 500000000) (-246263541 / 250000000) (Real.log (373419 / 1000000)) := by
  have h := reflection_log_15054_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15055_neg : (97534571 / 200000000) ≤ -Real.log (500000 / 814261) ∧
    -Real.log (500000 / 814261) ≤ (60959107 / 125000000) := by
  have h := checkLog_sound (w := (314261 / 1314261)) (n := 12)
    (lo := (97534571 / 200000000)) (hi := (60959107 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((814261 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(814261 / 500000) = 1/(500000 / 814261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15055 : Bounds (97534571 / 200000000) (60959107 / 125000000) (Real.log (814261 / 500000)) := by
  have h := reflection_log_15055_neg
  have he : Real.log (814261 / 500000) = -Real.log (500000 / 814261) := by
    rw [show ((814261 / 500000) : ℝ) = ((500000 / 814261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15056_neg : (198053127 / 200000000) ≤ -Real.log (185739 / 500000) ∧
    -Real.log (185739 / 500000) ≤ (990265637 / 1000000000) := by
  have h := checkLog_sound (w := (64261 / 435739)) (n := 12)
    (lo := (59423691 / 200000000)) (hi := (37139807 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 185739) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 185739) = 1/(185739 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15056 : Bounds (-990265637 / 1000000000) (-198053127 / 200000000) (Real.log (185739 / 500000)) := by
  have h := reflection_log_15056_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15057_neg : (25129639 / 50000000) ≤ -Real.log (151240023879 / 250000000000) ∧
    -Real.log (151240023879 / 250000000000) ≤ (502592781 / 1000000000) := by
  have h := checkLog_sound (w := (98759976121 / 401240023879)) (n := 12)
    (lo := (25129639 / 50000000)) (hi := (502592781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 151240023879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 151240023879) = 1/(151240023879 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15057 : Bounds (-502592781 / 1000000000) (-25129639 / 50000000) (Real.log (151240023879 / 250000000000)) := by
  have h := reflection_log_15057_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15058_neg : (498573899 / 1000000000) ≤ -Real.log (607396250439 / 1000000000000) ∧
    -Real.log (607396250439 / 1000000000000) ≤ (4985739 / 10000000) := by
  have h := checkLog_sound (w := (392603749561 / 1607396250439)) (n := 12)
    (lo := (498573899 / 1000000000)) (hi := (4985739 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 607396250439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 607396250439) = 1/(607396250439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15058 : Bounds (-4985739 / 10000000) (-498573899 / 1000000000) (Real.log (607396250439 / 1000000000000)) := by
  have h := reflection_log_15058_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15059_neg : (147153443 / 100000000) ≤ -Real.log (62500000000 / 272244616637) ∧
    -Real.log (62500000000 / 272244616637) ≤ (1471534433 / 1000000000) := by
  have h := checkLog_sound (w := (22244616637 / 522244616637)) (n := 12)
    (lo := (8524007 / 100000000)) (hi := (85240071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272244616637 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(272244616637 / 250000000000) = 1/(62500000000 / 272244616637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15059 : Bounds (147153443 / 100000000) (1471534433 / 1000000000) (Real.log (272244616637 / 62500000000)) := by
  have h := reflection_log_15059_neg
  have he : Real.log (272244616637 / 62500000000) = -Real.log (62500000000 / 272244616637) := by
    rw [show ((272244616637 / 62500000000) : ℝ) = ((62500000000 / 272244616637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15060_neg : (1477938489 / 1000000000) ≤ -Real.log (250000000000 / 1095974727979) ∧
    -Real.log (250000000000 / 1095974727979) ≤ (369484623 / 250000000) := by
  have h := checkLog_sound (w := (95974727979 / 2095974727979)) (n := 12)
    (lo := (91644129 / 1000000000)) (hi := (9164413 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1095974727979 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1095974727979 / 1000000000000) = 1/(250000000000 / 1095974727979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15060 : Bounds (1477938489 / 1000000000) (369484623 / 250000000) (Real.log (1095974727979 / 250000000000)) := by
  have h := reflection_log_15060_neg
  have he : Real.log (1095974727979 / 250000000000) = -Real.log (250000000000 / 1095974727979) := by
    rw [show ((1095974727979 / 250000000000) : ℝ) = ((250000000000 / 1095974727979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15061_neg : (568228063 / 125000000) ≤ -Real.log (500000000000 / 47119047619047) ∧
    -Real.log (500000000000 / 47119047619047) ≤ (4545824511 / 1000000000) := by
  have h := checkLog_sound (w := (15119047619047 / 79119047619047)) (n := 12)
    (lo := (24183839 / 62500000)) (hi := (15477657 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47119047619047 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(47119047619047 / 32000000000000) = 1/(500000000000 / 47119047619047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15061 : Bounds (568228063 / 125000000) (4545824511 / 1000000000) (Real.log (47119047619047 / 500000000000)) := by
  have h := reflection_log_15061_neg
  have he : Real.log (47119047619047 / 500000000000) = -Real.log (500000000000 / 47119047619047) := by
    rw [show ((47119047619047 / 500000000000) : ℝ) = ((500000000000 / 47119047619047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15062_neg : (2297559923 / 500000000) ≤ -Real.log (1 / 99) ∧
    -Real.log (1 / 99) ≤ (4595119853 / 1000000000) := by
  have h := checkLog_sound (w := (35 / 163)) (n := 12)
    (lo := (218118383 / 500000000)) (hi := (436236767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99 / 64) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(99 / 64) = 1/(1 / 99) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15062 : Bounds (2297559923 / 500000000) (4595119853 / 1000000000) (Real.log (99 / 1)) := by
  have h := reflection_log_15062_neg
  have he : Real.log (99 / 1) = -Real.log (1 / 99) := by
    rw [show ((99 / 1) : ℝ) = ((1 / 99) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15063_neg : (683601767 / 1000000000) ≤ -Real.log (1000 / 1981) ∧
    -Real.log (1000 / 1981) ≤ (85450221 / 125000000) := by
  have h := checkLog_sound (w := (981 / 2981)) (n := 12)
    (lo := (683601767 / 1000000000)) (hi := (85450221 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981 / 1000) = 1/(1000 / 1981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15063 : Bounds (683601767 / 1000000000) (85450221 / 125000000) (Real.log (1981 / 1000)) := by
  have h := reflection_log_15063_neg
  have he : Real.log (1981 / 1000) = -Real.log (1000 / 1981) := by
    rw [show ((1981 / 1000) : ℝ) = ((1000 / 1981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15064_neg : (3963316297 / 1000000000) ≤ -Real.log (19 / 1000) ∧
    -Real.log (19 / 1000) ≤ (3963316303 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 201)) (n := 12)
    (lo := (497580397 / 1000000000)) (hi := (248790199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 76) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 76) = 1/(19 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15064 : Bounds (-3963316303 / 1000000000) (-3963316297 / 1000000000) (Real.log (19 / 1000)) := by
  have h := reflection_log_15064_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15065_neg : (980519 / 1000000000) ≤ -Real.log (1000000 / 1000981) ∧
    -Real.log (1000000 / 1000981) ≤ (24513 / 25000000) := by
  have h := checkLog_sound (w := (981 / 2000981)) (n := 12)
    (lo := (980519 / 1000000000)) (hi := (24513 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000981 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000981 / 1000000) = 1/(1000000 / 1000981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15065 : Bounds (980519 / 1000000000) (24513 / 25000000) (Real.log (1000981 / 1000000)) := by
  have h := reflection_log_15065_neg
  have he : Real.log (1000981 / 1000000) = -Real.log (1000000 / 1000981) := by
    rw [show ((1000981 / 1000000) : ℝ) = ((1000000 / 1000981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15066_neg : (981481 / 1000000000) ≤ -Real.log (999019 / 1000000) ∧
    -Real.log (999019 / 1000000) ≤ (490741 / 500000000) := by
  have h := checkLog_sound (w := (981 / 1999019)) (n := 12)
    (lo := (981481 / 1000000000)) (hi := (490741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999019) = 1/(999019 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15066 : Bounds (-490741 / 500000000) (-981481 / 1000000000) (Real.log (999019 / 1000000)) := by
  have h := reflection_log_15066_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15067_neg : (487279783 / 1000000000) ≤ -Real.log (500000 / 813941) ∧
    -Real.log (500000 / 813941) ≤ (60909973 / 125000000) := by
  have h := checkLog_sound (w := (313941 / 1313941)) (n := 12)
    (lo := (487279783 / 1000000000)) (hi := (60909973 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((813941 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(813941 / 500000) = 1/(500000 / 813941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15067 : Bounds (487279783 / 1000000000) (60909973 / 125000000) (Real.log (813941 / 500000)) := by
  have h := reflection_log_15067_neg
  have he : Real.log (813941 / 500000) = -Real.log (500000 / 813941) := by
    rw [show ((813941 / 500000) : ℝ) = ((500000 / 813941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15068_neg : (98854427 / 100000000) ≤ -Real.log (186059 / 500000) ∧
    -Real.log (186059 / 500000) ≤ (61784017 / 62500000) := by
  have h := checkLog_sound (w := (63941 / 436059)) (n := 12)
    (lo := (29539709 / 100000000)) (hi := (295397091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 186059) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 186059) = 1/(186059 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15068 : Bounds (-61784017 / 62500000) (-98854427 / 100000000) (Real.log (186059 / 500000)) := by
  have h := reflection_log_15068_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15069_neg : (488478169 / 1000000000) ≤ -Real.log (500000 / 814917) ∧
    -Real.log (500000 / 814917) ≤ (48847817 / 100000000) := by
  have h := checkLog_sound (w := (314917 / 1314917)) (n := 12)
    (lo := (488478169 / 1000000000)) (hi := (48847817 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((814917 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(814917 / 500000) = 1/(500000 / 814917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15069 : Bounds (488478169 / 1000000000) (48847817 / 100000000) (Real.log (814917 / 500000)) := by
  have h := reflection_log_15069_neg
  have he : Real.log (814917 / 500000) = -Real.log (500000 / 814917) := by
    rw [show ((814917 / 500000) : ℝ) = ((500000 / 814917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15070_neg : (248450931 / 250000000) ≤ -Real.log (185083 / 500000) ∧
    -Real.log (185083 / 500000) ≤ (496901863 / 500000000) := by
  have h := checkLog_sound (w := (64917 / 435083)) (n := 12)
    (lo := (9395517 / 31250000)) (hi := (60131309 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 185083) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 185083) = 1/(185083 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15070 : Bounds (-496901863 / 500000000) (-248450931 / 250000000) (Real.log (185083 / 500000)) := by
  have h := reflection_log_15070_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15071_neg : (126331389 / 250000000) ≤ -Real.log (150827283111 / 250000000000) ∧
    -Real.log (150827283111 / 250000000000) ≤ (505325557 / 1000000000) := by
  have h := checkLog_sound (w := (99172716889 / 400827283111)) (n := 12)
    (lo := (126331389 / 250000000)) (hi := (505325557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 150827283111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 150827283111) = 1/(150827283111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15071 : Bounds (-505325557 / 1000000000) (-126331389 / 250000000) (Real.log (150827283111 / 250000000000)) := by
  have h := reflection_log_15071_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15072_neg : (501264487 / 1000000000) ≤ -Real.log (151441048519 / 250000000000) ∧
    -Real.log (151441048519 / 250000000000) ≤ (62658061 / 125000000) := by
  have h := checkLog_sound (w := (98558951481 / 401441048519)) (n := 12)
    (lo := (501264487 / 1000000000)) (hi := (62658061 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 151441048519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 151441048519) = 1/(151441048519 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15072 : Bounds (-62658061 / 125000000) (-501264487 / 1000000000) (Real.log (151441048519 / 250000000000)) := by
  have h := reflection_log_15072_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15073_neg : (368956013 / 250000000) ≤ -Real.log (50000000000 / 218731961367) ∧
    -Real.log (50000000000 / 218731961367) ≤ (295164811 / 200000000) := by
  have h := checkLog_sound (w := (18731961367 / 418731961367)) (n := 12)
    (lo := (22382423 / 250000000)) (hi := (89529693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218731961367 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(218731961367 / 200000000000) = 1/(50000000000 / 218731961367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15073 : Bounds (368956013 / 250000000) (295164811 / 200000000) (Real.log (218731961367 / 50000000000)) := by
  have h := reflection_log_15073_neg
  have he : Real.log (218731961367 / 50000000000) = -Real.log (50000000000 / 218731961367) := by
    rw [show ((218731961367 / 50000000000) : ℝ) = ((50000000000 / 218731961367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15074_neg : (1482281893 / 1000000000) ≤ -Real.log (500000000000 / 2201490682559) ∧
    -Real.log (500000000000 / 2201490682559) ≤ (185285237 / 125000000) := by
  have h := checkLog_sound (w := (201490682559 / 4201490682559)) (n := 12)
    (lo := (95987533 / 1000000000)) (hi := (47993767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2201490682559 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2201490682559 / 2000000000000) = 1/(500000000000 / 2201490682559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15074 : Bounds (1482281893 / 1000000000) (185285237 / 125000000) (Real.log (2201490682559 / 500000000000)) := by
  have h := reflection_log_15074_neg
  have he : Real.log (2201490682559 / 500000000000) = -Real.log (500000000000 / 2201490682559) := by
    rw [show ((2201490682559 / 500000000000) : ℝ) = ((500000000000 / 2201490682559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15075_neg : (290432379 / 62500000) ≤ -Real.log (500000000000 / 52131578947369) ∧
    -Real.log (500000000000 / 52131578947369) ≤ (4646918071 / 1000000000) := by
  have h := checkLog_sound (w := (20131578947369 / 84131578947369)) (n := 12)
    (lo := (61004373 / 125000000)) (hi := (97606997 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52131578947369 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(52131578947369 / 32000000000000) = 1/(500000000000 / 52131578947369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15075 : Bounds (290432379 / 62500000) (4646918071 / 1000000000) (Real.log (52131578947369 / 500000000000)) := by
  have h := reflection_log_15075_neg
  have he : Real.log (52131578947369 / 500000000000) = -Real.log (500000000000 / 52131578947369) := by
    rw [show ((52131578947369 / 500000000000) : ℝ) = ((500000000000 / 52131578947369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15076_neg : (136821287 / 200000000) ≤ -Real.log (500 / 991) ∧
    -Real.log (500 / 991) ≤ (171026609 / 250000000) := by
  have h := checkLog_sound (w := (491 / 1491)) (n := 12)
    (lo := (136821287 / 200000000)) (hi := (171026609 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991 / 500) = 1/(500 / 991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15076 : Bounds (136821287 / 200000000) (171026609 / 250000000) (Real.log (991 / 500)) := by
  have h := reflection_log_15076_neg
  have he : Real.log (991 / 500) = -Real.log (500 / 991) := by
    rw [show ((991 / 500) : ℝ) = ((500 / 991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15077_neg : (2008691759 / 500000000) ≤ -Real.log (9 / 500) ∧
    -Real.log (9 / 500) ≤ (1004345881 / 250000000) := by
  have h := checkLog_sound (w := (53 / 197)) (n := 12)
    (lo := (275823809 / 500000000)) (hi := (551647619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 72) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 72) = 1/(9 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15077 : Bounds (-1004345881 / 250000000) (-2008691759 / 500000000) (Real.log (9 / 500)) := by
  have h := reflection_log_15077_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15078_neg : (490759 / 500000000) ≤ -Real.log (500000 / 500491) ∧
    -Real.log (500000 / 500491) ≤ (981519 / 1000000000) := by
  have h := checkLog_sound (w := (491 / 1000491)) (n := 12)
    (lo := (490759 / 500000000)) (hi := (981519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500491 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500491 / 500000) = 1/(500000 / 500491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15078 : Bounds (490759 / 500000000) (981519 / 1000000000) (Real.log (500491 / 500000)) := by
  have h := reflection_log_15078_neg
  have he : Real.log (500491 / 500000) = -Real.log (500000 / 500491) := by
    rw [show ((500491 / 500000) : ℝ) = ((500000 / 500491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15079_neg : (491241 / 500000000) ≤ -Real.log (499509 / 500000) ∧
    -Real.log (499509 / 500000) ≤ (982483 / 1000000000) := by
  have h := checkLog_sound (w := (491 / 999509)) (n := 12)
    (lo := (491241 / 500000000)) (hi := (982483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499509) = 1/(499509 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15079 : Bounds (-982483 / 1000000000) (-491241 / 500000000) (Real.log (499509 / 500000)) := by
  have h := reflection_log_15079_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15080_neg : (488085413 / 1000000000) ≤ -Real.log (500000 / 814597) ∧
    -Real.log (500000 / 814597) ≤ (244042707 / 500000000) := by
  have h := checkLog_sound (w := (314597 / 1314597)) (n := 12)
    (lo := (488085413 / 1000000000)) (hi := (244042707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((814597 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(814597 / 500000) = 1/(500000 / 814597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15080 : Bounds (488085413 / 1000000000) (244042707 / 500000000) (Real.log (814597 / 500000)) := by
  have h := reflection_log_15080_neg
  have he : Real.log (814597 / 500000) = -Real.log (500000 / 814597) := by
    rw [show ((814597 / 500000) : ℝ) = ((500000 / 814597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15081_neg : (992076263 / 1000000000) ≤ -Real.log (185403 / 500000) ∧
    -Real.log (185403 / 500000) ≤ (198415253 / 200000000) := by
  have h := checkLog_sound (w := (64597 / 435403)) (n := 12)
    (lo := (298929083 / 1000000000)) (hi := (74732271 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 185403) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 185403) = 1/(185403 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15081 : Bounds (-198415253 / 200000000) (-992076263 / 1000000000) (Real.log (185403 / 500000)) := by
  have h := reflection_log_15081_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15082_neg : (30580637 / 62500000) ≤ -Real.log (500000 / 815579) ∧
    -Real.log (500000 / 815579) ≤ (489290193 / 1000000000) := by
  have h := checkLog_sound (w := (315579 / 1315579)) (n := 12)
    (lo := (30580637 / 62500000)) (hi := (489290193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((815579 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(815579 / 500000) = 1/(500000 / 815579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15082 : Bounds (30580637 / 62500000) (489290193 / 1000000000) (Real.log (815579 / 500000)) := by
  have h := reflection_log_15082_neg
  have he : Real.log (815579 / 500000) = -Real.log (500000 / 815579) := by
    rw [show ((815579 / 500000) : ℝ) = ((500000 / 815579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15083_neg : (99738691 / 100000000) ≤ -Real.log (184421 / 500000) ∧
    -Real.log (184421 / 500000) ≤ (31168341 / 31250000) := by
  have h := checkLog_sound (w := (65579 / 434421)) (n := 12)
    (lo := (30423973 / 100000000)) (hi := (304239731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 184421) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 184421) = 1/(184421 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15083 : Bounds (-31168341 / 31250000) (-99738691 / 100000000) (Real.log (184421 / 500000)) := by
  have h := reflection_log_15083_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15084_neg : (254048359 / 500000000) ≤ -Real.log (150409894759 / 250000000000) ∧
    -Real.log (150409894759 / 250000000000) ≤ (508096719 / 1000000000) := by
  have h := checkLog_sound (w := (99590105241 / 400409894759)) (n := 12)
    (lo := (254048359 / 500000000)) (hi := (508096719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 150409894759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 150409894759) = 1/(150409894759 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15084 : Bounds (-508096719 / 1000000000) (-254048359 / 500000000) (Real.log (150409894759 / 250000000000)) := by
  have h := reflection_log_15084_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15085_neg : (10079817 / 20000000) ≤ -Real.log (151028727591 / 250000000000) ∧
    -Real.log (151028727591 / 250000000000) ≤ (503990851 / 1000000000) := by
  have h := checkLog_sound (w := (98971272409 / 401028727591)) (n := 12)
    (lo := (10079817 / 20000000)) (hi := (503990851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 151028727591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 151028727591) = 1/(151028727591 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15085 : Bounds (-503990851 / 1000000000) (-10079817 / 20000000) (Real.log (151028727591 / 250000000000)) := by
  have h := reflection_log_15085_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15086_neg : (1480161677 / 1000000000) ≤ -Real.log (500000000000 / 2196827990917) ∧
    -Real.log (500000000000 / 2196827990917) ≤ (18502021 / 12500000) := by
  have h := checkLog_sound (w := (196827990917 / 4196827990917)) (n := 12)
    (lo := (93867317 / 1000000000)) (hi := (46933659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2196827990917 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2196827990917 / 2000000000000) = 1/(500000000000 / 2196827990917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15086 : Bounds (1480161677 / 1000000000) (18502021 / 12500000) (Real.log (2196827990917 / 500000000000)) := by
  have h := reflection_log_15086_neg
  have he : Real.log (2196827990917 / 500000000000) = -Real.log (500000000000 / 2196827990917) := by
    rw [show ((2196827990917 / 500000000000) : ℝ) = ((500000000000 / 2196827990917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15087_neg : (1486677101 / 1000000000) ≤ -Real.log (500000000000 / 2211187988353) ∧
    -Real.log (500000000000 / 2211187988353) ≤ (92917319 / 62500000) := by
  have h := checkLog_sound (w := (211187988353 / 4211187988353)) (n := 12)
    (lo := (100382741 / 1000000000)) (hi := (50191371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2211187988353 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2211187988353 / 2000000000000) = 1/(500000000000 / 2211187988353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15087 : Bounds (1486677101 / 1000000000) (92917319 / 62500000) (Real.log (2211187988353 / 500000000000)) := by
  have h := reflection_log_15087_neg
  have he : Real.log (2211187988353 / 500000000000) = -Real.log (500000000000 / 2211187988353) := by
    rw [show ((2211187988353 / 500000000000) : ℝ) = ((500000000000 / 2211187988353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15088_neg : (290432379 / 62500000) ≤ -Real.log (62500000000 / 6516447368421) ∧
    -Real.log (62500000000 / 6516447368421) ≤ (4646918071 / 1000000000) := by
  have h := checkLog_sound (w := (2516447368421 / 10516447368421)) (n := 12)
    (lo := (61004373 / 125000000)) (hi := (97606997 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6516447368421 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(6516447368421 / 4000000000000) = 1/(62500000000 / 6516447368421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15088 : Bounds (290432379 / 62500000) (4646918071 / 1000000000) (Real.log (6516447368421 / 62500000000)) := by
  have h := reflection_log_15088_neg
  have he : Real.log (6516447368421 / 62500000000) = -Real.log (62500000000 / 6516447368421) := by
    rw [show ((6516447368421 / 62500000000) : ℝ) = ((62500000000 / 6516447368421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15089_neg : (4701489953 / 1000000000) ≤ -Real.log (125000000000 / 13763888888889) ∧
    -Real.log (125000000000 / 13763888888889) ≤ (117537249 / 25000000) := by
  have h := checkLog_sound (w := (5763888888889 / 21763888888889)) (n := 12)
    (lo := (542606873 / 1000000000)) (hi := (271303437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13763888888889 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(13763888888889 / 8000000000000) = 1/(125000000000 / 13763888888889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15089 : Bounds (4701489953 / 1000000000) (117537249 / 25000000) (Real.log (13763888888889 / 125000000000)) := by
  have h := reflection_log_15089_neg
  have he : Real.log (13763888888889 / 125000000000) = -Real.log (125000000000 / 13763888888889) := by
    rw [show ((13763888888889 / 125000000000) : ℝ) = ((125000000000 / 13763888888889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15090_neg : (684610849 / 1000000000) ≤ -Real.log (1000 / 1983) ∧
    -Real.log (1000 / 1983) ≤ (13692217 / 20000000) := by
  have h := checkLog_sound (w := (983 / 2983)) (n := 12)
    (lo := (684610849 / 1000000000)) (hi := (13692217 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1983 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1983 / 1000) = 1/(1000 / 1983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15090 : Bounds (684610849 / 1000000000) (13692217 / 20000000) (Real.log (1983 / 1000)) := by
  have h := reflection_log_15090_neg
  have he : Real.log (1983 / 1000) = -Real.log (1000 / 1983) := by
    rw [show ((1983 / 1000) : ℝ) = ((1000 / 1983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15091_neg : (1018635483 / 250000000) ≤ -Real.log (17 / 1000) ∧
    -Real.log (17 / 1000) ≤ (2037270969 / 500000000) := by
  have h := checkLog_sound (w := (57 / 193)) (n := 12)
    (lo := (38050377 / 62500000)) (hi := (608806033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 68) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 68) = 1/(17 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15091 : Bounds (-2037270969 / 500000000) (-1018635483 / 250000000) (Real.log (17 / 1000)) := by
  have h := reflection_log_15091_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15092_neg : (982517 / 1000000000) ≤ -Real.log (1000000 / 1000983) ∧
    -Real.log (1000000 / 1000983) ≤ (491259 / 500000000) := by
  have h := checkLog_sound (w := (983 / 2000983)) (n := 12)
    (lo := (982517 / 1000000000)) (hi := (491259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000983 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000983 / 1000000) = 1/(1000000 / 1000983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15092 : Bounds (982517 / 1000000000) (491259 / 500000000) (Real.log (1000983 / 1000000)) := by
  have h := reflection_log_15092_neg
  have he : Real.log (1000983 / 1000000) = -Real.log (1000000 / 1000983) := by
    rw [show ((1000983 / 1000000) : ℝ) = ((1000000 / 1000983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15093_neg : (983483 / 1000000000) ≤ -Real.log (999017 / 1000000) ∧
    -Real.log (999017 / 1000000) ≤ (245871 / 250000000) := by
  have h := checkLog_sound (w := (983 / 1999017)) (n := 12)
    (lo := (983483 / 1000000000)) (hi := (245871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999017) = 1/(999017 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15093 : Bounds (-245871 / 250000000) (-983483 / 1000000000) (Real.log (999017 / 1000000)) := by
  have h := reflection_log_15093_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15094_neg : (488898369 / 1000000000) ≤ -Real.log (1000000 / 1630519) ∧
    -Real.log (1000000 / 1630519) ≤ (48889837 / 100000000) := by
  have h := checkLog_sound (w := (630519 / 2630519)) (n := 12)
    (lo := (488898369 / 1000000000)) (hi := (48889837 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1630519 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1630519 / 1000000) = 1/(1000000 / 1630519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15094 : Bounds (488898369 / 1000000000) (48889837 / 100000000) (Real.log (1630519 / 1000000)) := by
  have h := reflection_log_15094_neg
  have he : Real.log (1630519 / 1000000) = -Real.log (1000000 / 1630519) := by
    rw [show ((1630519 / 1000000) : ℝ) = ((1000000 / 1630519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15095_neg : (24891399 / 25000000) ≤ -Real.log (369481 / 1000000) ∧
    -Real.log (369481 / 1000000) ≤ (497827981 / 500000000) := by
  have h := checkLog_sound (w := (130519 / 869481)) (n := 12)
    (lo := (15125439 / 50000000)) (hi := (302508781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 369481) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 369481) = 1/(369481 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15095 : Bounds (-497827981 / 500000000) (-24891399 / 25000000) (Real.log (369481 / 1000000)) := by
  have h := reflection_log_15095_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15096_neg : (245054453 / 500000000) ≤ -Real.log (500000 / 816247) ∧
    -Real.log (500000 / 816247) ≤ (490108907 / 1000000000) := by
  have h := checkLog_sound (w := (316247 / 1316247)) (n := 12)
    (lo := (245054453 / 500000000)) (hi := (490108907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((816247 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(816247 / 500000) = 1/(500000 / 816247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15096 : Bounds (245054453 / 500000000) (490108907 / 1000000000) (Real.log (816247 / 500000)) := by
  have h := reflection_log_15096_neg
  have he : Real.log (816247 / 500000) = -Real.log (500000 / 816247) := by
    rw [show ((816247 / 500000) : ℝ) = ((500000 / 816247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15097_neg : (1001015633 / 1000000000) ≤ -Real.log (183753 / 500000) ∧
    -Real.log (183753 / 500000) ≤ (200203127 / 200000000) := by
  have h := checkLog_sound (w := (66247 / 433753)) (n := 12)
    (lo := (307868453 / 1000000000)) (hi := (153934227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 183753) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 183753) = 1/(183753 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15097 : Bounds (-200203127 / 200000000) (-1001015633 / 1000000000) (Real.log (183753 / 500000)) := by
  have h := reflection_log_15097_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15098_neg : (510906727 / 1000000000) ≤ -Real.log (149987834991 / 250000000000) ∧
    -Real.log (149987834991 / 250000000000) ≤ (63863341 / 125000000) := by
  have h := checkLog_sound (w := (100012165009 / 399987834991)) (n := 12)
    (lo := (510906727 / 1000000000)) (hi := (63863341 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 149987834991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 149987834991) = 1/(149987834991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15098 : Bounds (-63863341 / 125000000) (-510906727 / 1000000000) (Real.log (149987834991 / 250000000000)) := by
  have h := reflection_log_15098_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15099_neg : (506757591 / 1000000000) ≤ -Real.log (602445790639 / 1000000000000) ∧
    -Real.log (602445790639 / 1000000000000) ≤ (63344699 / 125000000) := by
  have h := checkLog_sound (w := (397554209361 / 1602445790639)) (n := 12)
    (lo := (506757591 / 1000000000)) (hi := (63344699 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 602445790639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 602445790639) = 1/(602445790639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15099 : Bounds (-63344699 / 125000000) (-506757591 / 1000000000) (Real.log (602445790639 / 1000000000000)) := by
  have h := reflection_log_15099_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15100_neg : (185569291 / 125000000) ≤ -Real.log (62500000000 / 275812389541) ∧
    -Real.log (62500000000 / 275812389541) ≤ (1484554331 / 1000000000) := by
  have h := checkLog_sound (w := (25812389541 / 525812389541)) (n := 12)
    (lo := (191914 / 1953125)) (hi := (98259969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((275812389541 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(275812389541 / 250000000000) = 1/(62500000000 / 275812389541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15100 : Bounds (185569291 / 125000000) (1484554331 / 1000000000) (Real.log (275812389541 / 62500000000)) := by
  have h := reflection_log_15100_neg
  have he : Real.log (275812389541 / 62500000000) = -Real.log (62500000000 / 275812389541) := by
    rw [show ((275812389541 / 62500000000) : ℝ) = ((62500000000 / 275812389541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15101_neg : (1491124539 / 1000000000) ≤ -Real.log (250000000000 / 1110522005083) ∧
    -Real.log (250000000000 / 1110522005083) ≤ (745562271 / 500000000) := by
  have h := checkLog_sound (w := (110522005083 / 2110522005083)) (n := 12)
    (lo := (104830179 / 1000000000)) (hi := (5241509 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1110522005083 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1110522005083 / 1000000000000) = 1/(250000000000 / 1110522005083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15101 : Bounds (1491124539 / 1000000000) (745562271 / 500000000) (Real.log (1110522005083 / 250000000000)) := by
  have h := reflection_log_15101_neg
  have he : Real.log (1110522005083 / 250000000000) = -Real.log (250000000000 / 1110522005083) := by
    rw [show ((1110522005083 / 250000000000) : ℝ) = ((250000000000 / 1110522005083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15102_neg : (4701489953 / 1000000000) ≤ -Real.log (100000000000 / 11011111111111) ∧
    -Real.log (100000000000 / 11011111111111) ≤ (117537249 / 25000000) := by
  have h := checkLog_sound (w := (4611111111111 / 17411111111111)) (n := 12)
    (lo := (542606873 / 1000000000)) (hi := (271303437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11011111111111 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(11011111111111 / 6400000000000) = 1/(100000000000 / 11011111111111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15102 : Bounds (4701489953 / 1000000000) (117537249 / 25000000) (Real.log (11011111111111 / 100000000000)) := by
  have h := reflection_log_15102_neg
  have he : Real.log (11011111111111 / 100000000000) = -Real.log (100000000000 / 11011111111111) := by
    rw [show ((11011111111111 / 100000000000) : ℝ) = ((100000000000 / 11011111111111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15103_neg : (4759152781 / 1000000000) ≤ -Real.log (100000000000 / 11664705882353) ∧
    -Real.log (100000000000 / 11664705882353) ≤ (1189788197 / 250000000) := by
  have h := checkLog_sound (w := (5264705882353 / 18064705882353)) (n := 12)
    (lo := (600269701 / 1000000000)) (hi := (300134851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11664705882353 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(11664705882353 / 6400000000000) = 1/(100000000000 / 11664705882353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15103 : Bounds (4759152781 / 1000000000) (1189788197 / 250000000) (Real.log (11664705882353 / 100000000000)) := by
  have h := reflection_log_15103_neg
  have he : Real.log (11664705882353 / 100000000000) = -Real.log (100000000000 / 11664705882353) := by
    rw [show ((11664705882353 / 100000000000) : ℝ) = ((100000000000 / 11664705882353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
