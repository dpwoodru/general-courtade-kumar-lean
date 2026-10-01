import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6336_neg : (98601303 / 500000000) ≤ -Real.log (250000000000 / 304497697171) ∧
    -Real.log (250000000000 / 304497697171) ≤ (197202607 / 1000000000) := by
  have h := checkLog_sound (w := (54497697171 / 554497697171)) (n := 12)
    (lo := (98601303 / 500000000)) (hi := (197202607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304497697171 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304497697171 / 250000000000) = 1/(250000000000 / 304497697171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6336 : Bounds (98601303 / 500000000) (197202607 / 1000000000) (Real.log (304497697171 / 250000000000)) := by
  have h := reflection_log_6336_neg
  have he : Real.log (304497697171 / 250000000000) = -Real.log (250000000000 / 304497697171) := by
    rw [show ((304497697171 / 250000000000) : ℝ) = ((250000000000 / 304497697171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6337_neg : (197699417 / 1000000000) ≤ -Real.log (500000000000 / 609298025117) ∧
    -Real.log (500000000000 / 609298025117) ≤ (98849709 / 500000000) := by
  have h := checkLog_sound (w := (109298025117 / 1109298025117)) (n := 12)
    (lo := (197699417 / 1000000000)) (hi := (98849709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609298025117 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609298025117 / 500000000000) = 1/(500000000000 / 609298025117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6337 : Bounds (197699417 / 1000000000) (98849709 / 500000000) (Real.log (609298025117 / 500000000000)) := by
  have h := reflection_log_6337_neg
  have he : Real.log (609298025117 / 500000000000) = -Real.log (500000000000 / 609298025117) := by
    rw [show ((609298025117 / 500000000000) : ℝ) = ((500000000000 / 609298025117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6338_neg : (98972719 / 250000000) ≤ -Real.log (250000000000 / 371426795923) ∧
    -Real.log (250000000000 / 371426795923) ≤ (395890877 / 1000000000) := by
  have h := checkLog_sound (w := (121426795923 / 621426795923)) (n := 12)
    (lo := (98972719 / 250000000)) (hi := (395890877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((371426795923 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(371426795923 / 250000000000) = 1/(250000000000 / 371426795923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6338 : Bounds (98972719 / 250000000) (395890877 / 1000000000) (Real.log (371426795923 / 250000000000)) := by
  have h := reflection_log_6338_neg
  have he : Real.log (371426795923 / 250000000000) = -Real.log (250000000000 / 371426795923) := by
    rw [show ((371426795923 / 250000000000) : ℝ) = ((250000000000 / 371426795923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6339_neg : (19804941 / 50000000) ≤ -Real.log (500000000000 / 743008079553) ∧
    -Real.log (500000000000 / 743008079553) ≤ (396098821 / 1000000000) := by
  have h := checkLog_sound (w := (243008079553 / 1243008079553)) (n := 12)
    (lo := (19804941 / 50000000)) (hi := (396098821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743008079553 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743008079553 / 500000000000) = 1/(500000000000 / 743008079553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6339 : Bounds (19804941 / 50000000) (396098821 / 1000000000) (Real.log (743008079553 / 500000000000)) := by
  have h := reflection_log_6339_neg
  have he : Real.log (743008079553 / 500000000000) = -Real.log (500000000000 / 743008079553) := by
    rw [show ((743008079553 / 500000000000) : ℝ) = ((500000000000 / 743008079553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6340_neg : (178648151 / 1000000000) ≤ -Real.log (2500 / 2989) ∧
    -Real.log (2500 / 2989) ≤ (22331019 / 125000000) := by
  have h := checkLog_sound (w := (489 / 5489)) (n := 12)
    (lo := (178648151 / 1000000000)) (hi := (22331019 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2989 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2989 / 2500) = 1/(2500 / 2989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6340 : Bounds (178648151 / 1000000000) (22331019 / 125000000) (Real.log (2989 / 2500)) := by
  have h := reflection_log_6340_neg
  have he : Real.log (2989 / 2500) = -Real.log (2500 / 2989) := by
    rw [show ((2989 / 2500) : ℝ) = ((2500 / 2989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6341_neg : (217658621 / 1000000000) ≤ -Real.log (2011 / 2500) ∧
    -Real.log (2011 / 2500) ≤ (108829311 / 500000000) := by
  have h := checkLog_sound (w := (489 / 4511)) (n := 12)
    (lo := (217658621 / 1000000000)) (hi := (108829311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2011) = 1/(2011 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6341 : Bounds (-108829311 / 500000000) (-217658621 / 1000000000) (Real.log (2011 / 2500)) := by
  have h := reflection_log_6341_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6342_neg : (9779 / 50000000) ≤ -Real.log (2500000 / 2500489) ∧
    -Real.log (2500000 / 2500489) ≤ (195581 / 1000000000) := by
  have h := checkLog_sound (w := (489 / 5000489)) (n := 12)
    (lo := (9779 / 50000000)) (hi := (195581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500489 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500489 / 2500000) = 1/(2500000 / 2500489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6342 : Bounds (9779 / 50000000) (195581 / 1000000000) (Real.log (2500489 / 2500000)) := by
  have h := reflection_log_6342_neg
  have he : Real.log (2500489 / 2500000) = -Real.log (2500000 / 2500489) := by
    rw [show ((2500489 / 2500000) : ℝ) = ((2500000 / 2500489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6343_neg : (195619 / 1000000000) ≤ -Real.log (2499511 / 2500000) ∧
    -Real.log (2499511 / 2500000) ≤ (9781 / 50000000) := by
  have h := checkLog_sound (w := (489 / 4999511)) (n := 12)
    (lo := (195619 / 1000000000)) (hi := (9781 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499511) = 1/(2499511 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6343 : Bounds (-9781 / 50000000) (-195619 / 1000000000) (Real.log (2499511 / 2500000)) := by
  have h := reflection_log_6343_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6344_neg : (46897243 / 500000000) ≤ -Real.log (500000 / 549167) ∧
    -Real.log (500000 / 549167) ≤ (93794487 / 1000000000) := by
  have h := checkLog_sound (w := (49167 / 1049167)) (n := 12)
    (lo := (46897243 / 500000000)) (hi := (93794487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549167 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549167 / 500000) = 1/(500000 / 549167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6344 : Bounds (46897243 / 500000000) (93794487 / 1000000000) (Real.log (549167 / 500000)) := by
  have h := reflection_log_6344_neg
  have he : Real.log (549167 / 500000) = -Real.log (500000 / 549167) := by
    rw [show ((549167 / 500000) : ℝ) = ((500000 / 549167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6345_neg : (20702223 / 200000000) ≤ -Real.log (450833 / 500000) ∧
    -Real.log (450833 / 500000) ≤ (25877779 / 250000000) := by
  have h := checkLog_sound (w := (49167 / 950833)) (n := 12)
    (lo := (20702223 / 200000000)) (hi := (25877779 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450833) = 1/(450833 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6345 : Bounds (-25877779 / 250000000) (-20702223 / 200000000) (Real.log (450833 / 500000)) := by
  have h := reflection_log_6345_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6346_neg : (23504609 / 250000000) ≤ -Real.log (50000 / 54929) ∧
    -Real.log (50000 / 54929) ≤ (94018437 / 1000000000) := by
  have h := checkLog_sound (w := (4929 / 104929)) (n := 12)
    (lo := (23504609 / 250000000)) (hi := (94018437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54929 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54929 / 50000) = 1/(50000 / 54929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6346 : Bounds (23504609 / 250000000) (94018437 / 1000000000) (Real.log (54929 / 50000)) := by
  have h := reflection_log_6346_neg
  have he : Real.log (54929 / 50000) = -Real.log (50000 / 54929) := by
    rw [show ((54929 / 50000) : ℝ) = ((50000 / 54929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6347_neg : (103783981 / 1000000000) ≤ -Real.log (45071 / 50000) ∧
    -Real.log (45071 / 50000) ≤ (51891991 / 500000000) := by
  have h := checkLog_sound (w := (4929 / 95071)) (n := 12)
    (lo := (103783981 / 1000000000)) (hi := (51891991 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45071) = 1/(45071 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6347 : Bounds (-51891991 / 500000000) (-103783981 / 1000000000) (Real.log (45071 / 50000)) := by
  have h := reflection_log_6347_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6348_neg : (1220693 / 125000000) ≤ -Real.log (2475704959 / 2500000000) ∧
    -Real.log (2475704959 / 2500000000) ≤ (1953109 / 200000000) := by
  have h := checkLog_sound (w := (24295041 / 4975704959)) (n := 12)
    (lo := (1220693 / 125000000)) (hi := (1953109 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2475704959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2475704959) = 1/(2475704959 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6348 : Bounds (-1953109 / 200000000) (-1220693 / 125000000) (Real.log (2475704959 / 2500000000)) := by
  have h := reflection_log_6348_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6349_neg : (9716629 / 1000000000) ≤ -Real.log (247582606111 / 250000000000) ∧
    -Real.log (247582606111 / 250000000000) ≤ (971663 / 100000000) := by
  have h := checkLog_sound (w := (2417393889 / 497582606111)) (n := 12)
    (lo := (9716629 / 1000000000)) (hi := (971663 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247582606111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247582606111) = 1/(247582606111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6349 : Bounds (-971663 / 100000000) (-9716629 / 1000000000) (Real.log (247582606111 / 250000000000)) := by
  have h := reflection_log_6349_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6350_neg : (98652801 / 500000000) ≤ -Real.log (500000000000 / 609058121299) ∧
    -Real.log (500000000000 / 609058121299) ≤ (197305603 / 1000000000) := by
  have h := checkLog_sound (w := (109058121299 / 1109058121299)) (n := 12)
    (lo := (98652801 / 500000000)) (hi := (197305603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609058121299 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609058121299 / 500000000000) = 1/(500000000000 / 609058121299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6350 : Bounds (98652801 / 500000000) (197305603 / 1000000000) (Real.log (609058121299 / 500000000000)) := by
  have h := reflection_log_6350_neg
  have he : Real.log (609058121299 / 500000000000) = -Real.log (500000000000 / 609058121299) := by
    rw [show ((609058121299 / 500000000000) : ℝ) = ((500000000000 / 609058121299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6351_neg : (98901209 / 500000000) ≤ -Real.log (100000000000 / 121872157263) ∧
    -Real.log (100000000000 / 121872157263) ≤ (197802419 / 1000000000) := by
  have h := checkLog_sound (w := (21872157263 / 221872157263)) (n := 12)
    (lo := (98901209 / 500000000)) (hi := (197802419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121872157263 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121872157263 / 100000000000) = 1/(100000000000 / 121872157263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6351 : Bounds (98901209 / 500000000) (197802419 / 1000000000) (Real.log (121872157263 / 100000000000)) := by
  have h := reflection_log_6351_neg
  have he : Real.log (121872157263 / 100000000000) = -Real.log (100000000000 / 121872157263) := by
    rw [show ((121872157263 / 100000000000) : ℝ) = ((100000000000 / 121872157263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6352_neg : (19804941 / 50000000) ≤ -Real.log (7812500000 / 11609501243) ∧
    -Real.log (7812500000 / 11609501243) ≤ (396098821 / 1000000000) := by
  have h := checkLog_sound (w := (3797001243 / 19422001243)) (n := 12)
    (lo := (19804941 / 50000000)) (hi := (396098821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11609501243 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11609501243 / 7812500000) = 1/(7812500000 / 11609501243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6352 : Bounds (19804941 / 50000000) (396098821 / 1000000000) (Real.log (11609501243 / 7812500000)) := by
  have h := reflection_log_6352_neg
  have he : Real.log (11609501243 / 7812500000) = -Real.log (7812500000 / 11609501243) := by
    rw [show ((11609501243 / 7812500000) : ℝ) = ((7812500000 / 11609501243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6353_neg : (99076693 / 250000000) ≤ -Real.log (500000000000 / 743162605669) ∧
    -Real.log (500000000000 / 743162605669) ≤ (396306773 / 1000000000) := by
  have h := checkLog_sound (w := (243162605669 / 1243162605669)) (n := 12)
    (lo := (99076693 / 250000000)) (hi := (396306773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743162605669 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743162605669 / 500000000000) = 1/(500000000000 / 743162605669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6353 : Bounds (99076693 / 250000000) (396306773 / 1000000000) (Real.log (743162605669 / 500000000000)) := by
  have h := reflection_log_6353_neg
  have he : Real.log (743162605669 / 500000000000) = -Real.log (500000000000 / 743162605669) := by
    rw [show ((743162605669 / 500000000000) : ℝ) = ((500000000000 / 743162605669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6354_neg : (178731787 / 1000000000) ≤ -Real.log (10000 / 11957) ∧
    -Real.log (10000 / 11957) ≤ (44682947 / 250000000) := by
  have h := checkLog_sound (w := (1957 / 21957)) (n := 12)
    (lo := (178731787 / 1000000000)) (hi := (44682947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11957 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11957 / 10000) = 1/(10000 / 11957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6354 : Bounds (178731787 / 1000000000) (44682947 / 250000000) (Real.log (11957 / 10000)) := by
  have h := reflection_log_6354_neg
  have he : Real.log (11957 / 10000) = -Real.log (10000 / 11957) := by
    rw [show ((11957 / 10000) : ℝ) = ((10000 / 11957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6355_neg : (43556589 / 200000000) ≤ -Real.log (8043 / 10000) ∧
    -Real.log (8043 / 10000) ≤ (108891473 / 500000000) := by
  have h := checkLog_sound (w := (1957 / 18043)) (n := 12)
    (lo := (43556589 / 200000000)) (hi := (108891473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8043) = 1/(8043 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6355 : Bounds (-108891473 / 500000000) (-43556589 / 200000000) (Real.log (8043 / 10000)) := by
  have h := reflection_log_6355_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6356_neg : (1223 / 6250000) ≤ -Real.log (10000000 / 10001957) ∧
    -Real.log (10000000 / 10001957) ≤ (195681 / 1000000000) := by
  have h := checkLog_sound (w := (1957 / 20001957)) (n := 12)
    (lo := (1223 / 6250000)) (hi := (195681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001957 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001957 / 10000000) = 1/(10000000 / 10001957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6356 : Bounds (1223 / 6250000) (195681 / 1000000000) (Real.log (10001957 / 10000000)) := by
  have h := reflection_log_6356_neg
  have he : Real.log (10001957 / 10000000) = -Real.log (10000000 / 10001957) := by
    rw [show ((10001957 / 10000000) : ℝ) = ((10000000 / 10001957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6357_neg : (195719 / 1000000000) ≤ -Real.log (9998043 / 10000000) ∧
    -Real.log (9998043 / 10000000) ≤ (4893 / 25000000) := by
  have h := checkLog_sound (w := (1957 / 19998043)) (n := 12)
    (lo := (195719 / 1000000000)) (hi := (4893 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998043) = 1/(9998043 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6357 : Bounds (-4893 / 25000000) (-195719 / 1000000000) (Real.log (9998043 / 10000000)) := by
  have h := reflection_log_6357_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6358_neg : (93840919 / 1000000000) ≤ -Real.log (200000 / 219677) ∧
    -Real.log (200000 / 219677) ≤ (2346023 / 25000000) := by
  have h := checkLog_sound (w := (19677 / 419677)) (n := 12)
    (lo := (93840919 / 1000000000)) (hi := (2346023 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219677 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219677 / 200000) = 1/(200000 / 219677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6358 : Bounds (93840919 / 1000000000) (2346023 / 25000000) (Real.log (219677 / 200000)) := by
  have h := reflection_log_6358_neg
  have he : Real.log (219677 / 200000) = -Real.log (200000 / 219677) := by
    rw [show ((219677 / 200000) : ℝ) = ((200000 / 219677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6359_neg : (103567679 / 1000000000) ≤ -Real.log (180323 / 200000) ∧
    -Real.log (180323 / 200000) ≤ (323649 / 3125000) := by
  have h := checkLog_sound (w := (19677 / 380323)) (n := 12)
    (lo := (103567679 / 1000000000)) (hi := (323649 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180323) = 1/(180323 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6359 : Bounds (-323649 / 3125000) (-103567679 / 1000000000) (Real.log (180323 / 200000)) := by
  have h := reflection_log_6359_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6360_neg : (94064859 / 1000000000) ≤ -Real.log (1000000 / 1098631) ∧
    -Real.log (1000000 / 1098631) ≤ (4703243 / 50000000) := by
  have h := checkLog_sound (w := (98631 / 2098631)) (n := 12)
    (lo := (94064859 / 1000000000)) (hi := (4703243 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098631 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098631 / 1000000) = 1/(1000000 / 1098631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6360 : Bounds (94064859 / 1000000000) (4703243 / 50000000) (Real.log (1098631 / 1000000)) := by
  have h := reflection_log_6360_neg
  have he : Real.log (1098631 / 1000000) = -Real.log (1000000 / 1098631) := by
    rw [show ((1098631 / 1000000) : ℝ) = ((1000000 / 1098631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6361_neg : (1298007 / 12500000) ≤ -Real.log (901369 / 1000000) ∧
    -Real.log (901369 / 1000000) ≤ (103840561 / 1000000000) := by
  have h := checkLog_sound (w := (98631 / 1901369)) (n := 12)
    (lo := (1298007 / 12500000)) (hi := (103840561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901369) = 1/(901369 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6361 : Bounds (-103840561 / 1000000000) (-1298007 / 12500000) (Real.log (901369 / 1000000)) := by
  have h := reflection_log_6361_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6362_neg : (9775701 / 1000000000) ≤ -Real.log (990271925839 / 1000000000000) ∧
    -Real.log (990271925839 / 1000000000000) ≤ (4887851 / 500000000) := by
  have h := checkLog_sound (w := (9728074161 / 1990271925839)) (n := 12)
    (lo := (9775701 / 1000000000)) (hi := (4887851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990271925839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990271925839) = 1/(990271925839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6362 : Bounds (-4887851 / 500000000) (-9775701 / 1000000000) (Real.log (990271925839 / 1000000000000)) := by
  have h := reflection_log_6362_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6363_neg : (243169 / 25000000) ≤ -Real.log (39612815671 / 40000000000) ∧
    -Real.log (39612815671 / 40000000000) ≤ (9726761 / 1000000000) := by
  have h := checkLog_sound (w := (387184329 / 79612815671)) (n := 12)
    (lo := (243169 / 25000000)) (hi := (9726761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39612815671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39612815671) = 1/(39612815671 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6363 : Bounds (-9726761 / 1000000000) (-243169 / 25000000) (Real.log (39612815671 / 40000000000)) := by
  have h := reflection_log_6363_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6364_neg : (98704299 / 500000000) ≤ -Real.log (250000000000 / 304560427677) ∧
    -Real.log (250000000000 / 304560427677) ≤ (197408599 / 1000000000) := by
  have h := checkLog_sound (w := (54560427677 / 554560427677)) (n := 12)
    (lo := (98704299 / 500000000)) (hi := (197408599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304560427677 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304560427677 / 250000000000) = 1/(250000000000 / 304560427677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6364 : Bounds (98704299 / 500000000) (197408599 / 1000000000) (Real.log (304560427677 / 250000000000)) := by
  have h := reflection_log_6364_neg
  have he : Real.log (304560427677 / 250000000000) = -Real.log (250000000000 / 304560427677) := by
    rw [show ((304560427677 / 250000000000) : ℝ) = ((250000000000 / 304560427677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6365_neg : (197905419 / 1000000000) ≤ -Real.log (62500000000 / 76177944327) ∧
    -Real.log (62500000000 / 76177944327) ≤ (9895271 / 50000000) := by
  have h := checkLog_sound (w := (13677944327 / 138677944327)) (n := 12)
    (lo := (197905419 / 1000000000)) (hi := (9895271 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76177944327 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76177944327 / 62500000000) = 1/(62500000000 / 76177944327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6365 : Bounds (197905419 / 1000000000) (9895271 / 50000000) (Real.log (76177944327 / 62500000000)) := by
  have h := reflection_log_6365_neg
  have he : Real.log (76177944327 / 62500000000) = -Real.log (62500000000 / 76177944327) := by
    rw [show ((76177944327 / 62500000000) : ℝ) = ((62500000000 / 76177944327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6366_neg : (99076693 / 250000000) ≤ -Real.log (125000000000 / 185790651417) ∧
    -Real.log (125000000000 / 185790651417) ≤ (396306773 / 1000000000) := by
  have h := checkLog_sound (w := (60790651417 / 310790651417)) (n := 12)
    (lo := (99076693 / 250000000)) (hi := (396306773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((185790651417 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(185790651417 / 125000000000) = 1/(125000000000 / 185790651417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6366 : Bounds (99076693 / 250000000) (396306773 / 1000000000) (Real.log (185790651417 / 125000000000)) := by
  have h := reflection_log_6366_neg
  have he : Real.log (185790651417 / 125000000000) = -Real.log (125000000000 / 185790651417) := by
    rw [show ((185790651417 / 125000000000) : ℝ) = ((125000000000 / 185790651417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6367_neg : (396514733 / 1000000000) ≤ -Real.log (500000000000 / 743317170211) ∧
    -Real.log (500000000000 / 743317170211) ≤ (198257367 / 500000000) := by
  have h := checkLog_sound (w := (243317170211 / 1243317170211)) (n := 12)
    (lo := (396514733 / 1000000000)) (hi := (198257367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743317170211 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743317170211 / 500000000000) = 1/(500000000000 / 743317170211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6367 : Bounds (396514733 / 1000000000) (198257367 / 500000000) (Real.log (743317170211 / 500000000000)) := by
  have h := reflection_log_6367_neg
  have he : Real.log (743317170211 / 500000000000) = -Real.log (500000000000 / 743317170211) := by
    rw [show ((743317170211 / 500000000000) : ℝ) = ((500000000000 / 743317170211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6368_neg : (178815417 / 1000000000) ≤ -Real.log (5000 / 5979) ∧
    -Real.log (5000 / 5979) ≤ (89407709 / 500000000) := by
  have h := checkLog_sound (w := (979 / 10979)) (n := 12)
    (lo := (178815417 / 1000000000)) (hi := (89407709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5979 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5979 / 5000) = 1/(5000 / 5979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6368 : Bounds (178815417 / 1000000000) (89407709 / 500000000) (Real.log (5979 / 5000)) := by
  have h := reflection_log_6368_neg
  have he : Real.log (5979 / 5000) = -Real.log (5000 / 5979) := by
    rw [show ((5979 / 5000) : ℝ) = ((5000 / 5979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6369_neg : (54476821 / 250000000) ≤ -Real.log (4021 / 5000) ∧
    -Real.log (4021 / 5000) ≤ (43581457 / 200000000) := by
  have h := checkLog_sound (w := (979 / 9021)) (n := 12)
    (lo := (54476821 / 250000000)) (hi := (43581457 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4021) = 1/(4021 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6369 : Bounds (-43581457 / 200000000) (-54476821 / 250000000) (Real.log (4021 / 5000)) := by
  have h := reflection_log_6369_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6370_neg : (9789 / 50000000) ≤ -Real.log (5000000 / 5000979) ∧
    -Real.log (5000000 / 5000979) ≤ (195781 / 1000000000) := by
  have h := checkLog_sound (w := (979 / 10000979)) (n := 12)
    (lo := (9789 / 50000000)) (hi := (195781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000979 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000979 / 5000000) = 1/(5000000 / 5000979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6370 : Bounds (9789 / 50000000) (195781 / 1000000000) (Real.log (5000979 / 5000000)) := by
  have h := reflection_log_6370_neg
  have he : Real.log (5000979 / 5000000) = -Real.log (5000000 / 5000979) := by
    rw [show ((5000979 / 5000000) : ℝ) = ((5000000 / 5000979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6371_neg : (195819 / 1000000000) ≤ -Real.log (4999021 / 5000000) ∧
    -Real.log (4999021 / 5000000) ≤ (9791 / 50000000) := by
  have h := checkLog_sound (w := (979 / 9999021)) (n := 12)
    (lo := (195819 / 1000000000)) (hi := (9791 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999021) = 1/(4999021 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6371 : Bounds (-9791 / 50000000) (-195819 / 1000000000) (Real.log (4999021 / 5000000)) := by
  have h := reflection_log_6371_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6372_neg : (93887349 / 1000000000) ≤ -Real.log (250000 / 274609) ∧
    -Real.log (250000 / 274609) ≤ (1877747 / 20000000) := by
  have h := checkLog_sound (w := (24609 / 524609)) (n := 12)
    (lo := (93887349 / 1000000000)) (hi := (1877747 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274609 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274609 / 250000) = 1/(250000 / 274609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6372 : Bounds (93887349 / 1000000000) (1877747 / 20000000) (Real.log (274609 / 250000)) := by
  have h := reflection_log_6372_neg
  have he : Real.log (274609 / 250000) = -Real.log (250000 / 274609) := by
    rw [show ((274609 / 250000) : ℝ) = ((250000 / 274609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6373_neg : (51812123 / 500000000) ≤ -Real.log (225391 / 250000) ∧
    -Real.log (225391 / 250000) ≤ (103624247 / 1000000000) := by
  have h := checkLog_sound (w := (24609 / 475391)) (n := 12)
    (lo := (51812123 / 500000000)) (hi := (103624247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225391) = 1/(225391 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6373 : Bounds (-103624247 / 1000000000) (-51812123 / 500000000) (Real.log (225391 / 250000)) := by
  have h := reflection_log_6373_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6374_neg : (94111279 / 1000000000) ≤ -Real.log (500000 / 549341) ∧
    -Real.log (500000 / 549341) ≤ (1176391 / 12500000) := by
  have h := checkLog_sound (w := (49341 / 1049341)) (n := 12)
    (lo := (94111279 / 1000000000)) (hi := (1176391 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549341 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549341 / 500000) = 1/(500000 / 549341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6374 : Bounds (94111279 / 1000000000) (1176391 / 12500000) (Real.log (549341 / 500000)) := by
  have h := reflection_log_6374_neg
  have he : Real.log (549341 / 500000) = -Real.log (500000 / 549341) := by
    rw [show ((549341 / 500000) : ℝ) = ((500000 / 549341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6375_neg : (51948571 / 500000000) ≤ -Real.log (450659 / 500000) ∧
    -Real.log (450659 / 500000) ≤ (103897143 / 1000000000) := by
  have h := checkLog_sound (w := (49341 / 950659)) (n := 12)
    (lo := (51948571 / 500000000)) (hi := (103897143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450659) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450659) = 1/(450659 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6375 : Bounds (-103897143 / 1000000000) (-51948571 / 500000000) (Real.log (450659 / 500000)) := by
  have h := reflection_log_6375_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6376_neg : (4892931 / 500000000) ≤ -Real.log (247565465719 / 250000000000) ∧
    -Real.log (247565465719 / 250000000000) ≤ (9785863 / 1000000000) := by
  have h := checkLog_sound (w := (2434534281 / 497565465719)) (n := 12)
    (lo := (4892931 / 500000000)) (hi := (9785863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247565465719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247565465719) = 1/(247565465719 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6376 : Bounds (-9785863 / 1000000000) (-4892931 / 500000000) (Real.log (247565465719 / 250000000000)) := by
  have h := reflection_log_6376_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6377_neg : (152139 / 15625000) ≤ -Real.log (61894397119 / 62500000000) ∧
    -Real.log (61894397119 / 62500000000) ≤ (9736897 / 1000000000) := by
  have h := checkLog_sound (w := (605602881 / 124394397119)) (n := 12)
    (lo := (152139 / 15625000)) (hi := (9736897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61894397119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61894397119) = 1/(61894397119 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6377 : Bounds (-9736897 / 1000000000) (-152139 / 15625000) (Real.log (61894397119 / 62500000000)) := by
  have h := reflection_log_6377_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6378_neg : (39502319 / 200000000) ≤ -Real.log (100000000000 / 121836719301) ∧
    -Real.log (100000000000 / 121836719301) ≤ (49377899 / 250000000) := by
  have h := checkLog_sound (w := (21836719301 / 221836719301)) (n := 12)
    (lo := (39502319 / 200000000)) (hi := (49377899 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121836719301 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121836719301 / 100000000000) = 1/(100000000000 / 121836719301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6378 : Bounds (39502319 / 200000000) (49377899 / 250000000) (Real.log (121836719301 / 100000000000)) := by
  have h := reflection_log_6378_neg
  have he : Real.log (121836719301 / 100000000000) = -Real.log (100000000000 / 121836719301) := by
    rw [show ((121836719301 / 100000000000) : ℝ) = ((100000000000 / 121836719301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6379_neg : (99004211 / 500000000) ≤ -Real.log (500000000000 / 609486330019) ∧
    -Real.log (500000000000 / 609486330019) ≤ (198008423 / 1000000000) := by
  have h := checkLog_sound (w := (109486330019 / 1109486330019)) (n := 12)
    (lo := (99004211 / 500000000)) (hi := (198008423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609486330019 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609486330019 / 500000000000) = 1/(500000000000 / 609486330019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6379 : Bounds (99004211 / 500000000) (198008423 / 1000000000) (Real.log (609486330019 / 500000000000)) := by
  have h := reflection_log_6379_neg
  have he : Real.log (609486330019 / 500000000000) = -Real.log (500000000000 / 609486330019) := by
    rw [show ((609486330019 / 500000000000) : ℝ) = ((500000000000 / 609486330019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6380_neg : (396514733 / 1000000000) ≤ -Real.log (50000000000 / 74331717021) ∧
    -Real.log (50000000000 / 74331717021) ≤ (198257367 / 500000000) := by
  have h := checkLog_sound (w := (24331717021 / 124331717021)) (n := 12)
    (lo := (396514733 / 1000000000)) (hi := (198257367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74331717021 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74331717021 / 50000000000) = 1/(50000000000 / 74331717021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6380 : Bounds (396514733 / 1000000000) (198257367 / 500000000) (Real.log (74331717021 / 50000000000)) := by
  have h := reflection_log_6380_neg
  have he : Real.log (74331717021 / 50000000000) = -Real.log (50000000000 / 74331717021) := by
    rw [show ((74331717021 / 50000000000) : ℝ) = ((50000000000 / 74331717021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6381_neg : (396722701 / 1000000000) ≤ -Real.log (500000000000 / 743471773191) ∧
    -Real.log (500000000000 / 743471773191) ≤ (198361351 / 500000000) := by
  have h := checkLog_sound (w := (243471773191 / 1243471773191)) (n := 12)
    (lo := (396722701 / 1000000000)) (hi := (198361351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743471773191 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743471773191 / 500000000000) = 1/(500000000000 / 743471773191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6381 : Bounds (396722701 / 1000000000) (198361351 / 500000000) (Real.log (743471773191 / 500000000000)) := by
  have h := reflection_log_6381_neg
  have he : Real.log (743471773191 / 500000000000) = -Real.log (500000000000 / 743471773191) := by
    rw [show ((743471773191 / 500000000000) : ℝ) = ((500000000000 / 743471773191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6382_neg : (178899039 / 1000000000) ≤ -Real.log (10000 / 11959) ∧
    -Real.log (10000 / 11959) ≤ (1118119 / 6250000) := by
  have h := checkLog_sound (w := (1959 / 21959)) (n := 12)
    (lo := (178899039 / 1000000000)) (hi := (1118119 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11959 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11959 / 10000) = 1/(10000 / 11959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6382 : Bounds (178899039 / 1000000000) (1118119 / 6250000) (Real.log (11959 / 10000)) := by
  have h := reflection_log_6382_neg
  have he : Real.log (11959 / 10000) = -Real.log (10000 / 11959) := by
    rw [show ((11959 / 10000) : ℝ) = ((10000 / 11959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6383_neg : (218031639 / 1000000000) ≤ -Real.log (8041 / 10000) ∧
    -Real.log (8041 / 10000) ≤ (5450791 / 25000000) := by
  have h := checkLog_sound (w := (1959 / 18041)) (n := 12)
    (lo := (218031639 / 1000000000)) (hi := (5450791 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8041) = 1/(8041 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6383 : Bounds (-5450791 / 25000000) (-218031639 / 1000000000) (Real.log (8041 / 10000)) := by
  have h := reflection_log_6383_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6384_neg : (4897 / 25000000) ≤ -Real.log (10000000 / 10001959) ∧
    -Real.log (10000000 / 10001959) ≤ (195881 / 1000000000) := by
  have h := checkLog_sound (w := (1959 / 20001959)) (n := 12)
    (lo := (4897 / 25000000)) (hi := (195881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001959 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001959 / 10000000) = 1/(10000000 / 10001959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6384 : Bounds (4897 / 25000000) (195881 / 1000000000) (Real.log (10001959 / 10000000)) := by
  have h := reflection_log_6384_neg
  have he : Real.log (10001959 / 10000000) = -Real.log (10000000 / 10001959) := by
    rw [show ((10001959 / 10000000) : ℝ) = ((10000000 / 10001959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6385_neg : (195919 / 1000000000) ≤ -Real.log (9998041 / 10000000) ∧
    -Real.log (9998041 / 10000000) ≤ (2449 / 12500000) := by
  have h := checkLog_sound (w := (1959 / 19998041)) (n := 12)
    (lo := (195919 / 1000000000)) (hi := (2449 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998041) = 1/(9998041 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6385 : Bounds (-2449 / 12500000) (-195919 / 1000000000) (Real.log (9998041 / 10000000)) := by
  have h := reflection_log_6385_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6386_neg : (46966889 / 500000000) ≤ -Real.log (1000000 / 1098487) ∧
    -Real.log (1000000 / 1098487) ≤ (93933779 / 1000000000) := by
  have h := checkLog_sound (w := (98487 / 2098487)) (n := 12)
    (lo := (46966889 / 500000000)) (hi := (93933779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098487 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098487 / 1000000) = 1/(1000000 / 1098487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6386 : Bounds (46966889 / 500000000) (93933779 / 1000000000) (Real.log (1098487 / 1000000)) := by
  have h := reflection_log_6386_neg
  have he : Real.log (1098487 / 1000000) = -Real.log (1000000 / 1098487) := by
    rw [show ((1098487 / 1000000) : ℝ) = ((1000000 / 1098487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6387_neg : (6480051 / 62500000) ≤ -Real.log (901513 / 1000000) ∧
    -Real.log (901513 / 1000000) ≤ (103680817 / 1000000000) := by
  have h := checkLog_sound (w := (98487 / 1901513)) (n := 12)
    (lo := (6480051 / 62500000)) (hi := (103680817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901513) = 1/(901513 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6387 : Bounds (-103680817 / 1000000000) (-6480051 / 62500000) (Real.log (901513 / 1000000)) := by
  have h := reflection_log_6387_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6388_neg : (94157697 / 1000000000) ≤ -Real.log (1000000 / 1098733) ∧
    -Real.log (1000000 / 1098733) ≤ (47078849 / 500000000) := by
  have h := checkLog_sound (w := (98733 / 2098733)) (n := 12)
    (lo := (94157697 / 1000000000)) (hi := (47078849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098733 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098733 / 1000000) = 1/(1000000 / 1098733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6388 : Bounds (94157697 / 1000000000) (47078849 / 500000000) (Real.log (1098733 / 1000000)) := by
  have h := reflection_log_6388_neg
  have he : Real.log (1098733 / 1000000) = -Real.log (1000000 / 1098733) := by
    rw [show ((1098733 / 1000000) : ℝ) = ((1000000 / 1098733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6389_neg : (103953727 / 1000000000) ≤ -Real.log (901267 / 1000000) ∧
    -Real.log (901267 / 1000000) ≤ (1624277 / 15625000) := by
  have h := checkLog_sound (w := (98733 / 1901267)) (n := 12)
    (lo := (103953727 / 1000000000)) (hi := (1624277 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901267) = 1/(901267 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6389 : Bounds (-1624277 / 15625000) (-103953727 / 1000000000) (Real.log (901267 / 1000000)) := by
  have h := reflection_log_6389_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6390_neg : (979603 / 100000000) ≤ -Real.log (990251794711 / 1000000000000) ∧
    -Real.log (990251794711 / 1000000000000) ≤ (9796031 / 1000000000) := by
  have h := checkLog_sound (w := (9748205289 / 1990251794711)) (n := 12)
    (lo := (979603 / 100000000)) (hi := (9796031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990251794711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990251794711) = 1/(990251794711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6390 : Bounds (-9796031 / 1000000000) (-979603 / 100000000) (Real.log (990251794711 / 1000000000000)) := by
  have h := reflection_log_6390_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6391_neg : (9747037 / 1000000000) ≤ -Real.log (990300310831 / 1000000000000) ∧
    -Real.log (990300310831 / 1000000000000) ≤ (4873519 / 500000000) := by
  have h := checkLog_sound (w := (9699689169 / 1990300310831)) (n := 12)
    (lo := (9747037 / 1000000000)) (hi := (4873519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990300310831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990300310831) = 1/(990300310831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6391 : Bounds (-4873519 / 500000000) (-9747037 / 1000000000) (Real.log (990300310831 / 1000000000000)) := by
  have h := reflection_log_6391_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6392_neg : (98807297 / 500000000) ≤ -Real.log (100000000000 / 121849268951) ∧
    -Real.log (100000000000 / 121849268951) ≤ (39522919 / 200000000) := by
  have h := checkLog_sound (w := (21849268951 / 221849268951)) (n := 12)
    (lo := (98807297 / 500000000)) (hi := (39522919 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((121849268951 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(121849268951 / 100000000000) = 1/(100000000000 / 121849268951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6392 : Bounds (98807297 / 500000000) (39522919 / 200000000) (Real.log (121849268951 / 100000000000)) := by
  have h := reflection_log_6392_neg
  have he : Real.log (121849268951 / 100000000000) = -Real.log (100000000000 / 121849268951) := by
    rw [show ((121849268951 / 100000000000) : ℝ) = ((100000000000 / 121849268951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6393_neg : (7924457 / 40000000) ≤ -Real.log (31250000000 / 38096819533) ∧
    -Real.log (31250000000 / 38096819533) ≤ (99055713 / 500000000) := by
  have h := checkLog_sound (w := (6846819533 / 69346819533)) (n := 12)
    (lo := (7924457 / 40000000)) (hi := (99055713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38096819533 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38096819533 / 31250000000) = 1/(31250000000 / 38096819533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6393 : Bounds (7924457 / 40000000) (99055713 / 500000000) (Real.log (38096819533 / 31250000000)) := by
  have h := reflection_log_6393_neg
  have he : Real.log (38096819533 / 31250000000) = -Real.log (31250000000 / 38096819533) := by
    rw [show ((38096819533 / 31250000000) : ℝ) = ((31250000000 / 38096819533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6394_neg : (396722701 / 1000000000) ≤ -Real.log (50000000000 / 74347177319) ∧
    -Real.log (50000000000 / 74347177319) ≤ (198361351 / 500000000) := by
  have h := checkLog_sound (w := (24347177319 / 124347177319)) (n := 12)
    (lo := (396722701 / 1000000000)) (hi := (198361351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74347177319 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74347177319 / 50000000000) = 1/(50000000000 / 74347177319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6394 : Bounds (396722701 / 1000000000) (198361351 / 500000000) (Real.log (74347177319 / 50000000000)) := by
  have h := reflection_log_6394_neg
  have he : Real.log (74347177319 / 50000000000) = -Real.log (50000000000 / 74347177319) := by
    rw [show ((74347177319 / 50000000000) : ℝ) = ((50000000000 / 74347177319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6395_neg : (396930679 / 1000000000) ≤ -Real.log (250000000000 / 371813207313) ∧
    -Real.log (250000000000 / 371813207313) ≤ (9923267 / 25000000) := by
  have h := checkLog_sound (w := (121813207313 / 621813207313)) (n := 12)
    (lo := (396930679 / 1000000000)) (hi := (9923267 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((371813207313 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(371813207313 / 250000000000) = 1/(250000000000 / 371813207313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6395 : Bounds (396930679 / 1000000000) (9923267 / 25000000) (Real.log (371813207313 / 250000000000)) := by
  have h := reflection_log_6395_neg
  have he : Real.log (371813207313 / 250000000000) = -Real.log (250000000000 / 371813207313) := by
    rw [show ((371813207313 / 250000000000) : ℝ) = ((250000000000 / 371813207313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6396_neg : (35796531 / 200000000) ≤ -Real.log (250 / 299) ∧
    -Real.log (250 / 299) ≤ (699151 / 3906250) := by
  have h := checkLog_sound (w := (49 / 549)) (n := 12)
    (lo := (35796531 / 200000000)) (hi := (699151 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299 / 250) = 1/(250 / 299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6396 : Bounds (35796531 / 200000000) (699151 / 3906250) (Real.log (299 / 250)) := by
  have h := reflection_log_6396_neg
  have he : Real.log (299 / 250) = -Real.log (250 / 299) := by
    rw [show ((299 / 250) : ℝ) = ((250 / 299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6397_neg : (218156009 / 1000000000) ≤ -Real.log (201 / 250) ∧
    -Real.log (201 / 250) ≤ (21815601 / 100000000) := by
  have h := checkLog_sound (w := (49 / 451)) (n := 12)
    (lo := (218156009 / 1000000000)) (hi := (21815601 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 201) = 1/(201 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6397 : Bounds (-21815601 / 100000000) (-218156009 / 1000000000) (Real.log (201 / 250)) := by
  have h := reflection_log_6397_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6398_neg : (9799 / 50000000) ≤ -Real.log (250000 / 250049) ∧
    -Real.log (250000 / 250049) ≤ (195981 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 500049)) (n := 12)
    (lo := (9799 / 50000000)) (hi := (195981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250049 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250049 / 250000) = 1/(250000 / 250049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6398 : Bounds (9799 / 50000000) (195981 / 1000000000) (Real.log (250049 / 250000)) := by
  have h := reflection_log_6398_neg
  have he : Real.log (250049 / 250000) = -Real.log (250000 / 250049) := by
    rw [show ((250049 / 250000) : ℝ) = ((250000 / 250049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6399_neg : (196019 / 1000000000) ≤ -Real.log (249951 / 250000) ∧
    -Real.log (249951 / 250000) ≤ (9801 / 50000000) := by
  have h := checkLog_sound (w := (49 / 499951)) (n := 12)
    (lo := (196019 / 1000000000)) (hi := (9801 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249951) = 1/(249951 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6399 : Bounds (-9801 / 50000000) (-196019 / 1000000000) (Real.log (249951 / 250000)) := by
  have h := reflection_log_6399_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
