import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6464_neg : (397762673 / 1000000000) ≤ -Real.log (250000000000 / 372122682593) ∧
    -Real.log (250000000000 / 372122682593) ≤ (198881337 / 500000000) := by
  have h := checkLog_sound (w := (122122682593 / 622122682593)) (n := 12)
    (lo := (397762673 / 1000000000)) (hi := (198881337 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372122682593 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372122682593 / 250000000000) = 1/(250000000000 / 372122682593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6464 : Bounds (397762673 / 1000000000) (198881337 / 500000000) (Real.log (372122682593 / 250000000000)) := by
  have h := reflection_log_6464_neg
  have he : Real.log (372122682593 / 250000000000) = -Real.log (250000000000 / 372122682593) := by
    rw [show ((372122682593 / 250000000000) : ℝ) = ((250000000000 / 372122682593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6465_neg : (397970693 / 1000000000) ≤ -Real.log (100000000000 / 148880039821) ∧
    -Real.log (100000000000 / 148880039821) ≤ (198985347 / 500000000) := by
  have h := checkLog_sound (w := (48880039821 / 248880039821)) (n := 12)
    (lo := (397970693 / 1000000000)) (hi := (198985347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148880039821 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148880039821 / 100000000000) = 1/(100000000000 / 148880039821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6465 : Bounds (397970693 / 1000000000) (198985347 / 500000000) (Real.log (148880039821 / 100000000000)) := by
  have h := reflection_log_6465_neg
  have he : Real.log (148880039821 / 100000000000) = -Real.log (100000000000 / 148880039821) := by
    rw [show ((148880039821 / 100000000000) : ℝ) = ((100000000000 / 148880039821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6466_neg : (44850157 / 250000000) ≤ -Real.log (2000 / 2393) ∧
    -Real.log (2000 / 2393) ≤ (179400629 / 1000000000) := by
  have h := checkLog_sound (w := (393 / 4393)) (n := 12)
    (lo := (44850157 / 250000000)) (hi := (179400629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2393 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2393 / 2000) = 1/(2000 / 2393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6466 : Bounds (44850157 / 250000000) (179400629 / 1000000000) (Real.log (2393 / 2000)) := by
  have h := reflection_log_6466_neg
  have he : Real.log (2393 / 2000) = -Real.log (2000 / 2393) := by
    rw [show ((2393 / 2000) : ℝ) = ((2000 / 2393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6467_neg : (218778093 / 1000000000) ≤ -Real.log (1607 / 2000) ∧
    -Real.log (1607 / 2000) ≤ (109389047 / 500000000) := by
  have h := checkLog_sound (w := (393 / 3607)) (n := 12)
    (lo := (218778093 / 1000000000)) (hi := (109389047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1607) = 1/(1607 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6467 : Bounds (-109389047 / 500000000) (-218778093 / 1000000000) (Real.log (1607 / 2000)) := by
  have h := reflection_log_6467_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6468_neg : (307 / 1562500) ≤ -Real.log (2000000 / 2000393) ∧
    -Real.log (2000000 / 2000393) ≤ (196481 / 1000000000) := by
  have h := checkLog_sound (w := (393 / 4000393)) (n := 12)
    (lo := (307 / 1562500)) (hi := (196481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000393 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000393 / 2000000) = 1/(2000000 / 2000393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6468 : Bounds (307 / 1562500) (196481 / 1000000000) (Real.log (2000393 / 2000000)) := by
  have h := reflection_log_6468_neg
  have he : Real.log (2000393 / 2000000) = -Real.log (2000000 / 2000393) := by
    rw [show ((2000393 / 2000000) : ℝ) = ((2000000 / 2000393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6469_neg : (196519 / 1000000000) ≤ -Real.log (1999607 / 2000000) ∧
    -Real.log (1999607 / 2000000) ≤ (4913 / 25000000) := by
  have h := checkLog_sound (w := (393 / 3999607)) (n := 12)
    (lo := (196519 / 1000000000)) (hi := (4913 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999607) = 1/(1999607 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6469 : Bounds (-4913 / 25000000) (-196519 / 1000000000) (Real.log (1999607 / 2000000)) := by
  have h := reflection_log_6469_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6470_neg : (5888269 / 62500000) ≤ -Real.log (1000000 / 1098793) ∧
    -Real.log (1000000 / 1098793) ≤ (18842461 / 200000000) := by
  have h := checkLog_sound (w := (98793 / 2098793)) (n := 12)
    (lo := (5888269 / 62500000)) (hi := (18842461 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098793 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098793 / 1000000) = 1/(1000000 / 1098793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6470 : Bounds (5888269 / 62500000) (18842461 / 200000000) (Real.log (1098793 / 1000000)) := by
  have h := reflection_log_6470_neg
  have he : Real.log (1098793 / 1000000) = -Real.log (1000000 / 1098793) := by
    rw [show ((1098793 / 1000000) : ℝ) = ((1000000 / 1098793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6471_neg : (104020303 / 1000000000) ≤ -Real.log (901207 / 1000000) ∧
    -Real.log (901207 / 1000000) ≤ (6501269 / 62500000) := by
  have h := checkLog_sound (w := (98793 / 1901207)) (n := 12)
    (lo := (104020303 / 1000000000)) (hi := (6501269 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901207) = 1/(901207 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6471 : Bounds (-6501269 / 62500000) (-104020303 / 1000000000) (Real.log (901207 / 1000000)) := by
  have h := reflection_log_6471_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6472_neg : (94437071 / 1000000000) ≤ -Real.log (6250 / 6869) ∧
    -Real.log (6250 / 6869) ≤ (5902317 / 62500000) := by
  have h := checkLog_sound (w := (619 / 13119)) (n := 12)
    (lo := (94437071 / 1000000000)) (hi := (5902317 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6869 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6869 / 6250) = 1/(6250 / 6869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6472 : Bounds (94437071 / 1000000000) (5902317 / 62500000) (Real.log (6869 / 6250)) := by
  have h := reflection_log_6472_neg
  have he : Real.log (6869 / 6250) = -Real.log (6250 / 6869) := by
    rw [show ((6869 / 6250) : ℝ) = ((6250 / 6869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6473_neg : (104294417 / 1000000000) ≤ -Real.log (5631 / 6250) ∧
    -Real.log (5631 / 6250) ≤ (52147209 / 500000000) := by
  have h := checkLog_sound (w := (619 / 11881)) (n := 12)
    (lo := (104294417 / 1000000000)) (hi := (52147209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6250 / 5631) = 1/(5631 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6473 : Bounds (-52147209 / 500000000) (-104294417 / 1000000000) (Real.log (5631 / 6250)) := by
  have h := reflection_log_6473_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6474_neg : (1971469 / 200000000) ≤ -Real.log (38679339 / 39062500) ∧
    -Real.log (38679339 / 39062500) ≤ (4928673 / 500000000) := by
  have h := checkLog_sound (w := (383161 / 77741839)) (n := 12)
    (lo := (1971469 / 200000000)) (hi := (4928673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39062500 / 38679339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39062500 / 38679339) = 1/(38679339 / 39062500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6474 : Bounds (-4928673 / 500000000) (-1971469 / 200000000) (Real.log (38679339 / 39062500)) := by
  have h := reflection_log_6474_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6475_neg : (4903999 / 500000000) ≤ -Real.log (990239943151 / 1000000000000) ∧
    -Real.log (990239943151 / 1000000000000) ≤ (9807999 / 1000000000) := by
  have h := checkLog_sound (w := (9760056849 / 1990239943151)) (n := 12)
    (lo := (4903999 / 500000000)) (hi := (9807999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990239943151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990239943151) = 1/(990239943151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6475 : Bounds (-9807999 / 1000000000) (-4903999 / 500000000) (Real.log (990239943151 / 1000000000000)) := by
  have h := reflection_log_6475_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6476_neg : (198232607 / 1000000000) ≤ -Real.log (250000000000 / 304811491699) ∧
    -Real.log (250000000000 / 304811491699) ≤ (6194769 / 31250000) := by
  have h := checkLog_sound (w := (54811491699 / 554811491699)) (n := 12)
    (lo := (198232607 / 1000000000)) (hi := (6194769 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304811491699 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304811491699 / 250000000000) = 1/(250000000000 / 304811491699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6476 : Bounds (198232607 / 1000000000) (6194769 / 31250000) (Real.log (304811491699 / 250000000000)) := by
  have h := reflection_log_6476_neg
  have he : Real.log (304811491699 / 250000000000) = -Real.log (250000000000 / 304811491699) := by
    rw [show ((304811491699 / 250000000000) : ℝ) = ((250000000000 / 304811491699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6477_neg : (6210359 / 31250000) ≤ -Real.log (500000000000 / 609927188777) ∧
    -Real.log (500000000000 / 609927188777) ≤ (198731489 / 1000000000) := by
  have h := checkLog_sound (w := (109927188777 / 1109927188777)) (n := 12)
    (lo := (6210359 / 31250000)) (hi := (198731489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609927188777 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609927188777 / 500000000000) = 1/(500000000000 / 609927188777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6477 : Bounds (6210359 / 31250000) (198731489 / 1000000000) (Real.log (609927188777 / 500000000000)) := by
  have h := reflection_log_6477_neg
  have he : Real.log (609927188777 / 500000000000) = -Real.log (500000000000 / 609927188777) := by
    rw [show ((609927188777 / 500000000000) : ℝ) = ((500000000000 / 609927188777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6478_neg : (397970693 / 1000000000) ≤ -Real.log (7812500000 / 11631253111) ∧
    -Real.log (7812500000 / 11631253111) ≤ (198985347 / 500000000) := by
  have h := checkLog_sound (w := (3818753111 / 19443753111)) (n := 12)
    (lo := (397970693 / 1000000000)) (hi := (198985347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11631253111 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11631253111 / 7812500000) = 1/(7812500000 / 11631253111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6478 : Bounds (397970693 / 1000000000) (198985347 / 500000000) (Real.log (11631253111 / 7812500000)) := by
  have h := reflection_log_6478_neg
  have he : Real.log (11631253111 / 7812500000) = -Real.log (7812500000 / 11631253111) := by
    rw [show ((11631253111 / 7812500000) : ℝ) = ((7812500000 / 11631253111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6479_neg : (199089361 / 500000000) ≤ -Real.log (250000000000 / 372277535781) ∧
    -Real.log (250000000000 / 372277535781) ≤ (398178723 / 1000000000) := by
  have h := checkLog_sound (w := (122277535781 / 622277535781)) (n := 12)
    (lo := (199089361 / 500000000)) (hi := (398178723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372277535781 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372277535781 / 250000000000) = 1/(250000000000 / 372277535781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6479 : Bounds (199089361 / 500000000) (398178723 / 1000000000) (Real.log (372277535781 / 250000000000)) := by
  have h := reflection_log_6479_neg
  have he : Real.log (372277535781 / 250000000000) = -Real.log (250000000000 / 372277535781) := by
    rw [show ((372277535781 / 250000000000) : ℝ) = ((250000000000 / 372277535781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6480_neg : (179484201 / 1000000000) ≤ -Real.log (5000 / 5983) ∧
    -Real.log (5000 / 5983) ≤ (89742101 / 500000000) := by
  have h := checkLog_sound (w := (983 / 10983)) (n := 12)
    (lo := (179484201 / 1000000000)) (hi := (89742101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5983 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5983 / 5000) = 1/(5000 / 5983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6480 : Bounds (179484201 / 1000000000) (89742101 / 500000000) (Real.log (5983 / 5000)) := by
  have h := reflection_log_6480_neg
  have he : Real.log (5983 / 5000) = -Real.log (5000 / 5983) := by
    rw [show ((5983 / 5000) : ℝ) = ((5000 / 5983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6481_neg : (218902557 / 1000000000) ≤ -Real.log (4017 / 5000) ∧
    -Real.log (4017 / 5000) ≤ (109451279 / 500000000) := by
  have h := checkLog_sound (w := (983 / 9017)) (n := 12)
    (lo := (218902557 / 1000000000)) (hi := (109451279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4017) = 1/(4017 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6481 : Bounds (-109451279 / 500000000) (-218902557 / 1000000000) (Real.log (4017 / 5000)) := by
  have h := reflection_log_6481_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6482_neg : (9829 / 50000000) ≤ -Real.log (5000000 / 5000983) ∧
    -Real.log (5000000 / 5000983) ≤ (196581 / 1000000000) := by
  have h := checkLog_sound (w := (983 / 10000983)) (n := 12)
    (lo := (9829 / 50000000)) (hi := (196581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000983 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000983 / 5000000) = 1/(5000000 / 5000983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6482 : Bounds (9829 / 50000000) (196581 / 1000000000) (Real.log (5000983 / 5000000)) := by
  have h := reflection_log_6482_neg
  have he : Real.log (5000983 / 5000000) = -Real.log (5000000 / 5000983) := by
    rw [show ((5000983 / 5000000) : ℝ) = ((5000000 / 5000983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6483_neg : (196619 / 1000000000) ≤ -Real.log (4999017 / 5000000) ∧
    -Real.log (4999017 / 5000000) ≤ (9831 / 50000000) := by
  have h := checkLog_sound (w := (983 / 9999017)) (n := 12)
    (lo := (196619 / 1000000000)) (hi := (9831 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999017) = 1/(4999017 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6483 : Bounds (-9831 / 50000000) (-196619 / 1000000000) (Real.log (4999017 / 5000000)) := by
  have h := reflection_log_6483_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6484_neg : (47129359 / 500000000) ≤ -Real.log (250000 / 274711) ∧
    -Real.log (250000 / 274711) ≤ (94258719 / 1000000000) := by
  have h := checkLog_sound (w := (24711 / 524711)) (n := 12)
    (lo := (47129359 / 500000000)) (hi := (94258719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((274711 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(274711 / 250000) = 1/(250000 / 274711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6484 : Bounds (47129359 / 500000000) (94258719 / 1000000000) (Real.log (274711 / 250000)) := by
  have h := reflection_log_6484_neg
  have he : Real.log (274711 / 250000) = -Real.log (250000 / 274711) := by
    rw [show ((274711 / 250000) : ℝ) = ((250000 / 274711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6485_neg : (20815379 / 200000000) ≤ -Real.log (225289 / 250000) ∧
    -Real.log (225289 / 250000) ≤ (3252403 / 31250000) := by
  have h := checkLog_sound (w := (24711 / 475289)) (n := 12)
    (lo := (20815379 / 200000000)) (hi := (3252403 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 225289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 225289) = 1/(225289 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6485 : Bounds (-3252403 / 31250000) (-20815379 / 200000000) (Real.log (225289 / 250000)) := by
  have h := reflection_log_6485_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6486_neg : (47241737 / 500000000) ≤ -Real.log (1000000 / 1099091) ∧
    -Real.log (1000000 / 1099091) ≤ (3779339 / 40000000) := by
  have h := checkLog_sound (w := (99091 / 2099091)) (n := 12)
    (lo := (47241737 / 500000000)) (hi := (3779339 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099091 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099091 / 1000000) = 1/(1000000 / 1099091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6486 : Bounds (47241737 / 500000000) (3779339 / 40000000) (Real.log (1099091 / 1000000)) := by
  have h := reflection_log_6486_neg
  have he : Real.log (1099091 / 1000000) = -Real.log (1000000 / 1099091) := by
    rw [show ((1099091 / 1000000) : ℝ) = ((1000000 / 1099091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6487_neg : (4174041 / 40000000) ≤ -Real.log (900909 / 1000000) ∧
    -Real.log (900909 / 1000000) ≤ (52175513 / 500000000) := by
  have h := checkLog_sound (w := (99091 / 1900909)) (n := 12)
    (lo := (4174041 / 40000000)) (hi := (52175513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900909) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900909) = 1/(900909 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6487 : Bounds (-52175513 / 500000000) (-4174041 / 40000000) (Real.log (900909 / 1000000)) := by
  have h := reflection_log_6487_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6488_neg : (197351 / 20000000) ≤ -Real.log (990180973719 / 1000000000000) ∧
    -Real.log (990180973719 / 1000000000000) ≤ (9867551 / 1000000000) := by
  have h := checkLog_sound (w := (9819026281 / 1990180973719)) (n := 12)
    (lo := (197351 / 20000000)) (hi := (9867551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990180973719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990180973719) = 1/(990180973719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6488 : Bounds (-9867551 / 1000000000) (-197351 / 20000000) (Real.log (990180973719 / 1000000000000)) := by
  have h := reflection_log_6488_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6489_neg : (9818177 / 1000000000) ≤ -Real.log (61889366479 / 62500000000) ∧
    -Real.log (61889366479 / 62500000000) ≤ (4909089 / 500000000) := by
  have h := checkLog_sound (w := (610633521 / 124389366479)) (n := 12)
    (lo := (9818177 / 1000000000)) (hi := (4909089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61889366479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61889366479) = 1/(61889366479 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6489 : Bounds (-4909089 / 500000000) (-9818177 / 1000000000) (Real.log (61889366479 / 62500000000)) := by
  have h := reflection_log_6489_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6490_neg : (198335613 / 1000000000) ≤ -Real.log (250000000000 / 304842890687) ∧
    -Real.log (250000000000 / 304842890687) ≤ (99167807 / 500000000) := by
  have h := checkLog_sound (w := (54842890687 / 554842890687)) (n := 12)
    (lo := (198335613 / 1000000000)) (hi := (99167807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304842890687 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(304842890687 / 250000000000) = 1/(250000000000 / 304842890687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6490 : Bounds (198335613 / 1000000000) (99167807 / 500000000) (Real.log (304842890687 / 250000000000)) := by
  have h := reflection_log_6490_neg
  have he : Real.log (304842890687 / 250000000000) = -Real.log (250000000000 / 304842890687) := by
    rw [show ((304842890687 / 250000000000) : ℝ) = ((250000000000 / 304842890687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6491_neg : (198834499 / 1000000000) ≤ -Real.log (50000000000 / 60999002119) ∧
    -Real.log (50000000000 / 60999002119) ≤ (397669 / 2000000) := by
  have h := checkLog_sound (w := (10999002119 / 110999002119)) (n := 12)
    (lo := (198834499 / 1000000000)) (hi := (397669 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((60999002119 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(60999002119 / 50000000000) = 1/(50000000000 / 60999002119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6491 : Bounds (198834499 / 1000000000) (397669 / 2000000) (Real.log (60999002119 / 50000000000)) := by
  have h := reflection_log_6491_neg
  have he : Real.log (60999002119 / 50000000000) = -Real.log (50000000000 / 60999002119) := by
    rw [show ((60999002119 / 50000000000) : ℝ) = ((50000000000 / 60999002119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6492_neg : (199089361 / 500000000) ≤ -Real.log (500000000000 / 744555071561) ∧
    -Real.log (500000000000 / 744555071561) ≤ (398178723 / 1000000000) := by
  have h := checkLog_sound (w := (244555071561 / 1244555071561)) (n := 12)
    (lo := (199089361 / 500000000)) (hi := (398178723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((744555071561 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(744555071561 / 500000000000) = 1/(500000000000 / 744555071561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6492 : Bounds (199089361 / 500000000) (398178723 / 1000000000) (Real.log (744555071561 / 500000000000)) := by
  have h := reflection_log_6492_neg
  have he : Real.log (744555071561 / 500000000000) = -Real.log (500000000000 / 744555071561) := by
    rw [show ((744555071561 / 500000000000) : ℝ) = ((500000000000 / 744555071561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6493_neg : (398386759 / 1000000000) ≤ -Real.log (20000000000 / 29788399303) ∧
    -Real.log (20000000000 / 29788399303) ≤ (9959669 / 25000000) := by
  have h := checkLog_sound (w := (9788399303 / 49788399303)) (n := 12)
    (lo := (398386759 / 1000000000)) (hi := (9959669 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29788399303 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29788399303 / 20000000000) = 1/(20000000000 / 29788399303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6493 : Bounds (398386759 / 1000000000) (9959669 / 25000000) (Real.log (29788399303 / 20000000000)) := by
  have h := reflection_log_6493_neg
  have he : Real.log (29788399303 / 20000000000) = -Real.log (20000000000 / 29788399303) := by
    rw [show ((29788399303 / 20000000000) : ℝ) = ((20000000000 / 29788399303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6494_neg : (22445971 / 125000000) ≤ -Real.log (10000 / 11967) ∧
    -Real.log (10000 / 11967) ≤ (179567769 / 1000000000) := by
  have h := checkLog_sound (w := (1967 / 21967)) (n := 12)
    (lo := (22445971 / 125000000)) (hi := (179567769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11967 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11967 / 10000) = 1/(10000 / 11967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6494 : Bounds (22445971 / 125000000) (179567769 / 1000000000) (Real.log (11967 / 10000)) := by
  have h := reflection_log_6494_neg
  have he : Real.log (11967 / 10000) = -Real.log (10000 / 11967) := by
    rw [show ((11967 / 10000) : ℝ) = ((10000 / 11967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6495_neg : (43805407 / 200000000) ≤ -Real.log (8033 / 10000) ∧
    -Real.log (8033 / 10000) ≤ (54756759 / 250000000) := by
  have h := checkLog_sound (w := (1967 / 18033)) (n := 12)
    (lo := (43805407 / 200000000)) (hi := (54756759 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8033) = 1/(8033 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6495 : Bounds (-54756759 / 250000000) (-43805407 / 200000000) (Real.log (8033 / 10000)) := by
  have h := reflection_log_6495_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6496_neg : (4917 / 25000000) ≤ -Real.log (10000000 / 10001967) ∧
    -Real.log (10000000 / 10001967) ≤ (196681 / 1000000000) := by
  have h := checkLog_sound (w := (1967 / 20001967)) (n := 12)
    (lo := (4917 / 25000000)) (hi := (196681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001967 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001967 / 10000000) = 1/(10000000 / 10001967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6496 : Bounds (4917 / 25000000) (196681 / 1000000000) (Real.log (10001967 / 10000000)) := by
  have h := reflection_log_6496_neg
  have he : Real.log (10001967 / 10000000) = -Real.log (10000000 / 10001967) := by
    rw [show ((10001967 / 10000000) : ℝ) = ((10000000 / 10001967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6497_neg : (196719 / 1000000000) ≤ -Real.log (9998033 / 10000000) ∧
    -Real.log (9998033 / 10000000) ≤ (2459 / 12500000) := by
  have h := checkLog_sound (w := (1967 / 19998033)) (n := 12)
    (lo := (196719 / 1000000000)) (hi := (2459 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998033) = 1/(9998033 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6497 : Bounds (-2459 / 12500000) (-196719 / 1000000000) (Real.log (9998033 / 10000000)) := by
  have h := reflection_log_6497_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6498_neg : (94305129 / 1000000000) ≤ -Real.log (200000 / 219779) ∧
    -Real.log (200000 / 219779) ≤ (9430513 / 100000000) := by
  have h := checkLog_sound (w := (19779 / 419779)) (n := 12)
    (lo := (94305129 / 1000000000)) (hi := (9430513 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219779 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219779 / 200000) = 1/(200000 / 219779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6498 : Bounds (94305129 / 1000000000) (9430513 / 100000000) (Real.log (219779 / 200000)) := by
  have h := reflection_log_6498_neg
  have he : Real.log (219779 / 200000) = -Real.log (200000 / 219779) := by
    rw [show ((219779 / 200000) : ℝ) = ((200000 / 219779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6499_neg : (10413349 / 100000000) ≤ -Real.log (180221 / 200000) ∧
    -Real.log (180221 / 200000) ≤ (104133491 / 1000000000) := by
  have h := checkLog_sound (w := (19779 / 380221)) (n := 12)
    (lo := (10413349 / 100000000)) (hi := (104133491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 180221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 180221) = 1/(180221 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6499 : Bounds (-104133491 / 1000000000) (-10413349 / 100000000) (Real.log (180221 / 200000)) := by
  have h := reflection_log_6499_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6500_neg : (756239 / 8000000) ≤ -Real.log (500000 / 549571) ∧
    -Real.log (500000 / 549571) ≤ (23632469 / 250000000) := by
  have h := checkLog_sound (w := (49571 / 1049571)) (n := 12)
    (lo := (756239 / 8000000)) (hi := (23632469 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549571 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549571 / 500000) = 1/(500000 / 549571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6500 : Bounds (756239 / 8000000) (23632469 / 250000000) (Real.log (549571 / 500000)) := by
  have h := reflection_log_6500_neg
  have he : Real.log (549571 / 500000) = -Real.log (500000 / 549571) := by
    rw [show ((549571 / 500000) : ℝ) = ((500000 / 549571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6501_neg : (26101909 / 250000000) ≤ -Real.log (450429 / 500000) ∧
    -Real.log (450429 / 500000) ≤ (104407637 / 1000000000) := by
  have h := checkLog_sound (w := (49571 / 950429)) (n := 12)
    (lo := (26101909 / 250000000)) (hi := (104407637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450429) = 1/(450429 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6501 : Bounds (-104407637 / 1000000000) (-26101909 / 250000000) (Real.log (450429 / 500000)) := by
  have h := reflection_log_6501_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6502_neg : (9877761 / 1000000000) ≤ -Real.log (247542715959 / 250000000000) ∧
    -Real.log (247542715959 / 250000000000) ≤ (4938881 / 500000000) := by
  have h := checkLog_sound (w := (2457284041 / 497542715959)) (n := 12)
    (lo := (9877761 / 1000000000)) (hi := (4938881 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247542715959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247542715959) = 1/(247542715959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6502 : Bounds (-4938881 / 500000000) (-9877761 / 1000000000) (Real.log (247542715959 / 250000000000)) := by
  have h := reflection_log_6502_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6503_neg : (9828361 / 1000000000) ≤ -Real.log (39608791159 / 40000000000) ∧
    -Real.log (39608791159 / 40000000000) ≤ (4914181 / 500000000) := by
  have h := checkLog_sound (w := (391208841 / 79608791159)) (n := 12)
    (lo := (9828361 / 1000000000)) (hi := (4914181 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39608791159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39608791159) = 1/(39608791159 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6503 : Bounds (-4914181 / 500000000) (-9828361 / 1000000000) (Real.log (39608791159 / 40000000000)) := by
  have h := reflection_log_6503_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6504_neg : (9921931 / 50000000) ≤ -Real.log (500000000000 / 609748586457) ∧
    -Real.log (500000000000 / 609748586457) ≤ (198438621 / 1000000000) := by
  have h := checkLog_sound (w := (109748586457 / 1109748586457)) (n := 12)
    (lo := (9921931 / 50000000)) (hi := (198438621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((609748586457 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(609748586457 / 500000000000) = 1/(500000000000 / 609748586457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6504 : Bounds (9921931 / 50000000) (198438621 / 1000000000) (Real.log (609748586457 / 500000000000)) := by
  have h := reflection_log_6504_neg
  have he : Real.log (609748586457 / 500000000000) = -Real.log (500000000000 / 609748586457) := by
    rw [show ((609748586457 / 500000000000) : ℝ) = ((500000000000 / 609748586457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6505_neg : (198937511 / 1000000000) ≤ -Real.log (250000000000 / 305026430359) ∧
    -Real.log (250000000000 / 305026430359) ≤ (24867189 / 125000000) := by
  have h := checkLog_sound (w := (55026430359 / 555026430359)) (n := 12)
    (lo := (198937511 / 1000000000)) (hi := (24867189 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305026430359 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305026430359 / 250000000000) = 1/(250000000000 / 305026430359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6505 : Bounds (198937511 / 1000000000) (24867189 / 125000000) (Real.log (305026430359 / 250000000000)) := by
  have h := reflection_log_6505_neg
  have he : Real.log (305026430359 / 250000000000) = -Real.log (250000000000 / 305026430359) := by
    rw [show ((305026430359 / 250000000000) : ℝ) = ((250000000000 / 305026430359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6506_neg : (398386759 / 1000000000) ≤ -Real.log (250000000000 / 372354991287) ∧
    -Real.log (250000000000 / 372354991287) ≤ (9959669 / 25000000) := by
  have h := checkLog_sound (w := (122354991287 / 622354991287)) (n := 12)
    (lo := (398386759 / 1000000000)) (hi := (9959669 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372354991287 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372354991287 / 250000000000) = 1/(250000000000 / 372354991287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6506 : Bounds (398386759 / 1000000000) (9959669 / 25000000) (Real.log (372354991287 / 250000000000)) := by
  have h := reflection_log_6506_neg
  have he : Real.log (372354991287 / 250000000000) = -Real.log (250000000000 / 372354991287) := by
    rw [show ((372354991287 / 250000000000) : ℝ) = ((250000000000 / 372354991287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6507_neg : (99648701 / 250000000) ≤ -Real.log (100000000000 / 148972986431) ∧
    -Real.log (100000000000 / 148972986431) ≤ (79718961 / 200000000) := by
  have h := checkLog_sound (w := (48972986431 / 248972986431)) (n := 12)
    (lo := (99648701 / 250000000)) (hi := (79718961 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148972986431 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148972986431 / 100000000000) = 1/(100000000000 / 148972986431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6507 : Bounds (99648701 / 250000000) (79718961 / 200000000) (Real.log (148972986431 / 100000000000)) := by
  have h := reflection_log_6507_neg
  have he : Real.log (148972986431 / 100000000000) = -Real.log (100000000000 / 148972986431) := by
    rw [show ((148972986431 / 100000000000) : ℝ) = ((100000000000 / 148972986431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6508_neg : (701763 / 3906250) ≤ -Real.log (625 / 748) ∧
    -Real.log (625 / 748) ≤ (179651329 / 1000000000) := by
  have h := checkLog_sound (w := (123 / 1373)) (n := 12)
    (lo := (701763 / 3906250)) (hi := (179651329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((748 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(748 / 625) = 1/(625 / 748) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6508 : Bounds (701763 / 3906250) (179651329 / 1000000000) (Real.log (748 / 625)) := by
  have h := reflection_log_6508_neg
  have he : Real.log (748 / 625) = -Real.log (625 / 748) := by
    rw [show ((748 / 625) : ℝ) = ((625 / 748) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6509_neg : (21915153 / 100000000) ≤ -Real.log (502 / 625) ∧
    -Real.log (502 / 625) ≤ (219151531 / 1000000000) := by
  have h := checkLog_sound (w := (123 / 1127)) (n := 12)
    (lo := (21915153 / 100000000)) (hi := (219151531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 502) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 502) = 1/(502 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6509 : Bounds (-219151531 / 1000000000) (-21915153 / 100000000) (Real.log (502 / 625)) := by
  have h := reflection_log_6509_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6510_neg : (9839 / 50000000) ≤ -Real.log (625000 / 625123) ∧
    -Real.log (625000 / 625123) ≤ (196781 / 1000000000) := by
  have h := checkLog_sound (w := (123 / 1250123)) (n := 12)
    (lo := (9839 / 50000000)) (hi := (196781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625123 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625123 / 625000) = 1/(625000 / 625123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6510 : Bounds (9839 / 50000000) (196781 / 1000000000) (Real.log (625123 / 625000)) := by
  have h := reflection_log_6510_neg
  have he : Real.log (625123 / 625000) = -Real.log (625000 / 625123) := by
    rw [show ((625123 / 625000) : ℝ) = ((625000 / 625123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6511_neg : (196819 / 1000000000) ≤ -Real.log (624877 / 625000) ∧
    -Real.log (624877 / 625000) ≤ (9841 / 50000000) := by
  have h := checkLog_sound (w := (123 / 1249877)) (n := 12)
    (lo := (196819 / 1000000000)) (hi := (9841 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624877) = 1/(624877 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6511 : Bounds (-9841 / 50000000) (-196819 / 1000000000) (Real.log (624877 / 625000)) := by
  have h := reflection_log_6511_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6512_neg : (47175769 / 500000000) ≤ -Real.log (500000 / 549473) ∧
    -Real.log (500000 / 549473) ≤ (94351539 / 1000000000) := by
  have h := checkLog_sound (w := (49473 / 1049473)) (n := 12)
    (lo := (47175769 / 500000000)) (hi := (94351539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((549473 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(549473 / 500000) = 1/(500000 / 549473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6512 : Bounds (47175769 / 500000000) (94351539 / 1000000000) (Real.log (549473 / 500000)) := by
  have h := reflection_log_6512_neg
  have he : Real.log (549473 / 500000) = -Real.log (500000 / 549473) := by
    rw [show ((549473 / 500000) : ℝ) = ((500000 / 549473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6513_neg : (104190089 / 1000000000) ≤ -Real.log (450527 / 500000) ∧
    -Real.log (450527 / 500000) ≤ (10419009 / 100000000) := by
  have h := checkLog_sound (w := (49473 / 950527)) (n := 12)
    (lo := (104190089 / 1000000000)) (hi := (10419009 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 450527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 450527) = 1/(450527 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6513 : Bounds (-10419009 / 100000000) (-104190089 / 1000000000) (Real.log (450527 / 500000)) := by
  have h := reflection_log_6513_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6514_neg : (47288137 / 500000000) ≤ -Real.log (1000000 / 1099193) ∧
    -Real.log (1000000 / 1099193) ≤ (3783051 / 40000000) := by
  have h := checkLog_sound (w := (99193 / 2099193)) (n := 12)
    (lo := (47288137 / 500000000)) (hi := (3783051 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1099193 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1099193 / 1000000) = 1/(1000000 / 1099193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6514 : Bounds (47288137 / 500000000) (3783051 / 40000000) (Real.log (1099193 / 1000000)) := by
  have h := reflection_log_6514_neg
  have he : Real.log (1099193 / 1000000) = -Real.log (1000000 / 1099193) := by
    rw [show ((1099193 / 1000000) : ℝ) = ((1000000 / 1099193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6515_neg : (417857 / 4000000) ≤ -Real.log (900807 / 1000000) ∧
    -Real.log (900807 / 1000000) ≤ (104464251 / 1000000000) := by
  have h := checkLog_sound (w := (99193 / 1900807)) (n := 12)
    (lo := (417857 / 4000000)) (hi := (104464251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 900807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 900807) = 1/(900807 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6515 : Bounds (-104464251 / 1000000000) (-417857 / 4000000) (Real.log (900807 / 1000000)) := by
  have h := reflection_log_6515_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6516_neg : (1235997 / 125000000) ≤ -Real.log (990160748751 / 1000000000000) ∧
    -Real.log (990160748751 / 1000000000000) ≤ (9887977 / 1000000000) := by
  have h := checkLog_sound (w := (9839251249 / 1990160748751)) (n := 12)
    (lo := (1235997 / 125000000)) (hi := (9887977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 990160748751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 990160748751) = 1/(990160748751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6516 : Bounds (-9887977 / 1000000000) (-1235997 / 125000000) (Real.log (990160748751 / 1000000000000)) := by
  have h := reflection_log_6516_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6517_neg : (9838551 / 1000000000) ≤ -Real.log (247552422271 / 250000000000) ∧
    -Real.log (247552422271 / 250000000000) ≤ (1229819 / 125000000) := by
  have h := checkLog_sound (w := (2447577729 / 497552422271)) (n := 12)
    (lo := (9838551 / 1000000000)) (hi := (1229819 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247552422271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247552422271) = 1/(247552422271 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6517 : Bounds (-1229819 / 125000000) (-9838551 / 1000000000) (Real.log (247552422271 / 250000000000)) := by
  have h := reflection_log_6517_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6518_neg : (49635407 / 250000000) ≤ -Real.log (10000000000 / 12196227973) ∧
    -Real.log (10000000000 / 12196227973) ≤ (198541629 / 1000000000) := by
  have h := checkLog_sound (w := (2196227973 / 22196227973)) (n := 12)
    (lo := (49635407 / 250000000)) (hi := (198541629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12196227973 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12196227973 / 10000000000) = 1/(10000000000 / 12196227973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6518 : Bounds (49635407 / 250000000) (198541629 / 1000000000) (Real.log (12196227973 / 10000000000)) := by
  have h := reflection_log_6518_neg
  have he : Real.log (12196227973 / 10000000000) = -Real.log (10000000000 / 12196227973) := by
    rw [show ((12196227973 / 10000000000) : ℝ) = ((10000000000 / 12196227973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6519_neg : (49760131 / 250000000) ≤ -Real.log (500000000000 / 610115707361) ∧
    -Real.log (500000000000 / 610115707361) ≤ (7961621 / 40000000) := by
  have h := checkLog_sound (w := (110115707361 / 1110115707361)) (n := 12)
    (lo := (49760131 / 250000000)) (hi := (7961621 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610115707361 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(610115707361 / 500000000000) = 1/(500000000000 / 610115707361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6519 : Bounds (49760131 / 250000000) (7961621 / 40000000) (Real.log (610115707361 / 500000000000)) := by
  have h := reflection_log_6519_neg
  have he : Real.log (610115707361 / 500000000000) = -Real.log (500000000000 / 610115707361) := by
    rw [show ((610115707361 / 500000000000) : ℝ) = ((500000000000 / 610115707361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6520_neg : (99648701 / 250000000) ≤ -Real.log (250000000000 / 372432466077) ∧
    -Real.log (250000000000 / 372432466077) ≤ (79718961 / 200000000) := by
  have h := checkLog_sound (w := (122432466077 / 622432466077)) (n := 12)
    (lo := (99648701 / 250000000)) (hi := (79718961 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372432466077 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372432466077 / 250000000000) = 1/(250000000000 / 372432466077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6520 : Bounds (99648701 / 250000000) (79718961 / 200000000) (Real.log (372432466077 / 250000000000)) := by
  have h := reflection_log_6520_neg
  have he : Real.log (372432466077 / 250000000000) = -Real.log (250000000000 / 372432466077) := by
    rw [show ((372432466077 / 250000000000) : ℝ) = ((250000000000 / 372432466077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6521_neg : (199401429 / 500000000) ≤ -Real.log (500000000000 / 745019920319) ∧
    -Real.log (500000000000 / 745019920319) ≤ (398802859 / 1000000000) := by
  have h := checkLog_sound (w := (245019920319 / 1245019920319)) (n := 12)
    (lo := (199401429 / 500000000)) (hi := (398802859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((745019920319 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(745019920319 / 500000000000) = 1/(500000000000 / 745019920319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6521 : Bounds (199401429 / 500000000) (398802859 / 1000000000) (Real.log (745019920319 / 500000000000)) := by
  have h := reflection_log_6521_neg
  have he : Real.log (745019920319 / 500000000000) = -Real.log (500000000000 / 745019920319) := by
    rw [show ((745019920319 / 500000000000) : ℝ) = ((500000000000 / 745019920319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6522_neg : (1123343 / 6250000) ≤ -Real.log (10000 / 11969) ∧
    -Real.log (10000 / 11969) ≤ (179734881 / 1000000000) := by
  have h := checkLog_sound (w := (1969 / 21969)) (n := 12)
    (lo := (1123343 / 6250000)) (hi := (179734881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11969 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11969 / 10000) = 1/(10000 / 11969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6522 : Bounds (1123343 / 6250000) (179734881 / 1000000000) (Real.log (11969 / 10000)) := by
  have h := reflection_log_6522_neg
  have he : Real.log (11969 / 10000) = -Real.log (10000 / 11969) := by
    rw [show ((11969 / 10000) : ℝ) = ((10000 / 11969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6523_neg : (219276039 / 1000000000) ≤ -Real.log (8031 / 10000) ∧
    -Real.log (8031 / 10000) ≤ (5481901 / 25000000) := by
  have h := checkLog_sound (w := (1969 / 18031)) (n := 12)
    (lo := (219276039 / 1000000000)) (hi := (5481901 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8031) = 1/(8031 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6523 : Bounds (-5481901 / 25000000) (-219276039 / 1000000000) (Real.log (8031 / 10000)) := by
  have h := reflection_log_6523_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6524_neg : (2461 / 12500000) ≤ -Real.log (10000000 / 10001969) ∧
    -Real.log (10000000 / 10001969) ≤ (196881 / 1000000000) := by
  have h := checkLog_sound (w := (1969 / 20001969)) (n := 12)
    (lo := (2461 / 12500000)) (hi := (196881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001969 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001969 / 10000000) = 1/(10000000 / 10001969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6524 : Bounds (2461 / 12500000) (196881 / 1000000000) (Real.log (10001969 / 10000000)) := by
  have h := reflection_log_6524_neg
  have he : Real.log (10001969 / 10000000) = -Real.log (10000000 / 10001969) := by
    rw [show ((10001969 / 10000000) : ℝ) = ((10000000 / 10001969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6525_neg : (196919 / 1000000000) ≤ -Real.log (9998031 / 10000000) ∧
    -Real.log (9998031 / 10000000) ≤ (4923 / 25000000) := by
  have h := checkLog_sound (w := (1969 / 19998031)) (n := 12)
    (lo := (196919 / 1000000000)) (hi := (4923 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998031) = 1/(9998031 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6525 : Bounds (-4923 / 25000000) (-196919 / 1000000000) (Real.log (9998031 / 10000000)) := by
  have h := reflection_log_6525_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6526_neg : (18879589 / 200000000) ≤ -Real.log (1000000 / 1098997) ∧
    -Real.log (1000000 / 1098997) ≤ (47198973 / 500000000) := by
  have h := checkLog_sound (w := (98997 / 2098997)) (n := 12)
    (lo := (18879589 / 200000000)) (hi := (47198973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1098997 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1098997 / 1000000) = 1/(1000000 / 1098997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6526 : Bounds (18879589 / 200000000) (47198973 / 500000000) (Real.log (1098997 / 1000000)) := by
  have h := reflection_log_6526_neg
  have he : Real.log (1098997 / 1000000) = -Real.log (1000000 / 1098997) := by
    rw [show ((1098997 / 1000000) : ℝ) = ((1000000 / 1098997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6527_neg : (104246691 / 1000000000) ≤ -Real.log (901003 / 1000000) ∧
    -Real.log (901003 / 1000000) ≤ (26061673 / 250000000) := by
  have h := checkLog_sound (w := (98997 / 1901003)) (n := 12)
    (lo := (104246691 / 1000000000)) (hi := (26061673 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 901003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 901003) = 1/(901003 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6527 : Bounds (-26061673 / 250000000) (-104246691 / 1000000000) (Real.log (901003 / 1000000)) := by
  have h := reflection_log_6527_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
