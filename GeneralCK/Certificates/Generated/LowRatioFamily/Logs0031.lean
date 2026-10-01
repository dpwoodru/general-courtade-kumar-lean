import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1984_neg : (33150087 / 200000000) ≤ -Real.log (500000000000 / 590139254389) ∧
    -Real.log (500000000000 / 590139254389) ≤ (41437609 / 250000000) := by
  have h := checkLog_sound (w := (90139254389 / 1090139254389)) (n := 12)
    (lo := (33150087 / 200000000)) (hi := (41437609 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590139254389 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590139254389 / 500000000000) = 1/(500000000000 / 590139254389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1984 : Bounds (33150087 / 200000000) (41437609 / 250000000) (Real.log (590139254389 / 500000000000)) := by
  have h := reflection_log_1984_neg
  have he : Real.log (590139254389 / 500000000000) = -Real.log (500000000000 / 590139254389) := by
    rw [show ((590139254389 / 500000000000) : ℝ) = ((500000000000 / 590139254389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1985_neg : (33160563 / 100000000) ≤ -Real.log (50000000000 / 69660165131) ∧
    -Real.log (50000000000 / 69660165131) ≤ (331605631 / 1000000000) := by
  have h := checkLog_sound (w := (19660165131 / 119660165131)) (n := 12)
    (lo := (33160563 / 100000000)) (hi := (331605631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69660165131 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69660165131 / 50000000000) = 1/(50000000000 / 69660165131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1985 : Bounds (33160563 / 100000000) (331605631 / 1000000000) (Real.log (69660165131 / 50000000000)) := by
  have h := reflection_log_1985_neg
  have he : Real.log (69660165131 / 50000000000) = -Real.log (50000000000 / 69660165131) := by
    rw [show ((69660165131 / 50000000000) : ℝ) = ((50000000000 / 69660165131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1986_neg : (165905591 / 500000000) ≤ -Real.log (250000000000 / 348372426999) ∧
    -Real.log (250000000000 / 348372426999) ≤ (331811183 / 1000000000) := by
  have h := checkLog_sound (w := (98372426999 / 598372426999)) (n := 12)
    (lo := (165905591 / 500000000)) (hi := (331811183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((348372426999 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(348372426999 / 250000000000) = 1/(250000000000 / 348372426999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1986 : Bounds (165905591 / 500000000) (331811183 / 1000000000) (Real.log (348372426999 / 250000000000)) := by
  have h := reflection_log_1986_neg
  have he : Real.log (348372426999 / 250000000000) = -Real.log (250000000000 / 348372426999) := by
    rw [show ((348372426999 / 250000000000) : ℝ) = ((250000000000 / 348372426999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1987_neg : (15229181 / 100000000) ≤ -Real.log (2000 / 2329) ∧
    -Real.log (2000 / 2329) ≤ (152291811 / 1000000000) := by
  have h := checkLog_sound (w := (329 / 4329)) (n := 12)
    (lo := (15229181 / 100000000)) (hi := (152291811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2329 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2329 / 2000) = 1/(2000 / 2329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1987 : Bounds (15229181 / 100000000) (152291811 / 1000000000) (Real.log (2329 / 2000)) := by
  have h := reflection_log_1987_neg
  have he : Real.log (2329 / 2000) = -Real.log (2000 / 2329) := by
    rw [show ((2329 / 2000) : ℝ) = ((2000 / 2329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1988_neg : (17972493 / 100000000) ≤ -Real.log (1671 / 2000) ∧
    -Real.log (1671 / 2000) ≤ (179724931 / 1000000000) := by
  have h := checkLog_sound (w := (329 / 3671)) (n := 12)
    (lo := (17972493 / 100000000)) (hi := (179724931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1671) = 1/(1671 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1988 : Bounds (-179724931 / 1000000000) (-17972493 / 100000000) (Real.log (1671 / 2000)) := by
  have h := reflection_log_1988_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1989_neg : (82243 / 500000000) ≤ -Real.log (2000000 / 2000329) ∧
    -Real.log (2000000 / 2000329) ≤ (164487 / 1000000000) := by
  have h := checkLog_sound (w := (329 / 4000329)) (n := 12)
    (lo := (82243 / 500000000)) (hi := (164487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000329 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000329 / 2000000) = 1/(2000000 / 2000329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1989 : Bounds (82243 / 500000000) (164487 / 1000000000) (Real.log (2000329 / 2000000)) := by
  have h := reflection_log_1989_neg
  have he : Real.log (2000329 / 2000000) = -Real.log (2000000 / 2000329) := by
    rw [show ((2000329 / 2000000) : ℝ) = ((2000000 / 2000329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1990_neg : (164513 / 1000000000) ≤ -Real.log (1999671 / 2000000) ∧
    -Real.log (1999671 / 2000000) ≤ (82257 / 500000000) := by
  have h := checkLog_sound (w := (329 / 3999671)) (n := 12)
    (lo := (164513 / 1000000000)) (hi := (82257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999671) = 1/(1999671 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1990 : Bounds (-82257 / 500000000) (-164513 / 1000000000) (Real.log (1999671 / 2000000)) := by
  have h := reflection_log_1990_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1991_neg : (1238961 / 15625000) ≤ -Real.log (500000 / 541261) ∧
    -Real.log (500000 / 541261) ≤ (15858701 / 200000000) := by
  have h := checkLog_sound (w := (41261 / 1041261)) (n := 12)
    (lo := (1238961 / 15625000)) (hi := (15858701 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541261 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541261 / 500000) = 1/(500000 / 541261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1991 : Bounds (1238961 / 15625000) (15858701 / 200000000) (Real.log (541261 / 500000)) := by
  have h := reflection_log_1991_neg
  have he : Real.log (541261 / 500000) = -Real.log (500000 / 541261) := by
    rw [show ((541261 / 500000) : ℝ) = ((500000 / 541261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1992_neg : (86126677 / 1000000000) ≤ -Real.log (458739 / 500000) ∧
    -Real.log (458739 / 500000) ≤ (43063339 / 500000000) := by
  have h := checkLog_sound (w := (41261 / 958739)) (n := 12)
    (lo := (86126677 / 1000000000)) (hi := (43063339 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458739) = 1/(458739 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1992 : Bounds (-43063339 / 500000000) (-86126677 / 1000000000) (Real.log (458739 / 500000)) := by
  have h := reflection_log_1992_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1993_neg : (39746047 / 500000000) ≤ -Real.log (1000000 / 1082737) ∧
    -Real.log (1000000 / 1082737) ≤ (15898419 / 200000000) := by
  have h := checkLog_sound (w := (82737 / 2082737)) (n := 12)
    (lo := (39746047 / 500000000)) (hi := (15898419 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082737 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082737 / 1000000) = 1/(1000000 / 1082737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1993 : Bounds (39746047 / 500000000) (15898419 / 200000000) (Real.log (1082737 / 1000000)) := by
  have h := reflection_log_1993_neg
  have he : Real.log (1082737 / 1000000) = -Real.log (1000000 / 1082737) := by
    rw [show ((1082737 / 1000000) : ℝ) = ((1000000 / 1082737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1994_neg : (86361043 / 1000000000) ≤ -Real.log (917263 / 1000000) ∧
    -Real.log (917263 / 1000000) ≤ (21590261 / 250000000) := by
  have h := checkLog_sound (w := (82737 / 1917263)) (n := 12)
    (lo := (86361043 / 1000000000)) (hi := (21590261 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917263) = 1/(917263 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1994 : Bounds (-21590261 / 250000000) (-86361043 / 1000000000) (Real.log (917263 / 1000000)) := by
  have h := reflection_log_1994_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1995_neg : (1717237 / 250000000) ≤ -Real.log (993154588831 / 1000000000000) ∧
    -Real.log (993154588831 / 1000000000000) ≤ (6868949 / 1000000000) := by
  have h := checkLog_sound (w := (6845411169 / 1993154588831)) (n := 12)
    (lo := (1717237 / 250000000)) (hi := (6868949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993154588831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993154588831) = 1/(993154588831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1995 : Bounds (-6868949 / 1000000000) (-1717237 / 250000000) (Real.log (993154588831 / 1000000000000)) := by
  have h := reflection_log_1995_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1996_neg : (6833173 / 1000000000) ≤ -Real.log (248297529879 / 250000000000) ∧
    -Real.log (248297529879 / 250000000000) ≤ (3416587 / 500000000) := by
  have h := checkLog_sound (w := (1702470121 / 498297529879)) (n := 12)
    (lo := (6833173 / 1000000000)) (hi := (3416587 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248297529879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248297529879) = 1/(248297529879 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1996 : Bounds (-3416587 / 500000000) (-6833173 / 1000000000) (Real.log (248297529879 / 250000000000)) := by
  have h := reflection_log_1996_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1997_neg : (165420181 / 1000000000) ≤ -Real.log (500000000000 / 589944391037) ∧
    -Real.log (500000000000 / 589944391037) ≤ (82710091 / 500000000) := by
  have h := checkLog_sound (w := (89944391037 / 1089944391037)) (n := 12)
    (lo := (165420181 / 1000000000)) (hi := (82710091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589944391037 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589944391037 / 500000000000) = 1/(500000000000 / 589944391037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1997 : Bounds (165420181 / 1000000000) (82710091 / 500000000) (Real.log (589944391037 / 500000000000)) := by
  have h := reflection_log_1997_neg
  have he : Real.log (589944391037 / 500000000000) = -Real.log (500000000000 / 589944391037) := by
    rw [show ((589944391037 / 500000000000) : ℝ) = ((500000000000 / 589944391037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1998_neg : (165853137 / 1000000000) ≤ -Real.log (250000000000 / 295099933171) ∧
    -Real.log (250000000000 / 295099933171) ≤ (82926569 / 500000000) := by
  have h := checkLog_sound (w := (45099933171 / 545099933171)) (n := 12)
    (lo := (165853137 / 1000000000)) (hi := (82926569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295099933171 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295099933171 / 250000000000) = 1/(250000000000 / 295099933171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1998 : Bounds (165853137 / 1000000000) (82926569 / 500000000) (Real.log (295099933171 / 250000000000)) := by
  have h := reflection_log_1998_neg
  have he : Real.log (295099933171 / 250000000000) = -Real.log (250000000000 / 295099933171) := by
    rw [show ((295099933171 / 250000000000) : ℝ) = ((250000000000 / 295099933171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1999_neg : (165905591 / 500000000) ≤ -Real.log (500000000000 / 696744853997) ∧
    -Real.log (500000000000 / 696744853997) ≤ (331811183 / 1000000000) := by
  have h := checkLog_sound (w := (196744853997 / 1196744853997)) (n := 12)
    (lo := (165905591 / 500000000)) (hi := (331811183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696744853997 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696744853997 / 500000000000) = 1/(500000000000 / 696744853997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1999 : Bounds (165905591 / 500000000) (331811183 / 1000000000) (Real.log (696744853997 / 500000000000)) := by
  have h := reflection_log_1999_neg
  have he : Real.log (696744853997 / 500000000000) = -Real.log (500000000000 / 696744853997) := by
    rw [show ((696744853997 / 500000000000) : ℝ) = ((500000000000 / 696744853997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2000_neg : (332016741 / 1000000000) ≤ -Real.log (125000000000 / 174222022741) ∧
    -Real.log (125000000000 / 174222022741) ≤ (166008371 / 500000000) := by
  have h := checkLog_sound (w := (49222022741 / 299222022741)) (n := 12)
    (lo := (332016741 / 1000000000)) (hi := (166008371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((174222022741 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(174222022741 / 125000000000) = 1/(125000000000 / 174222022741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2000 : Bounds (332016741 / 1000000000) (166008371 / 500000000) (Real.log (174222022741 / 125000000000)) := by
  have h := reflection_log_2000_neg
  have he : Real.log (174222022741 / 125000000000) = -Real.log (125000000000 / 174222022741) := by
    rw [show ((174222022741 / 125000000000) : ℝ) = ((125000000000 / 174222022741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2001_neg : (1904721 / 12500000) ≤ -Real.log (5000 / 5823) ∧
    -Real.log (5000 / 5823) ≤ (152377681 / 1000000000) := by
  have h := checkLog_sound (w := (823 / 10823)) (n := 12)
    (lo := (1904721 / 12500000)) (hi := (152377681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5823 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5823 / 5000) = 1/(5000 / 5823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2001 : Bounds (1904721 / 12500000) (152377681 / 1000000000) (Real.log (5823 / 5000)) := by
  have h := reflection_log_2001_neg
  have he : Real.log (5823 / 5000) = -Real.log (5000 / 5823) := by
    rw [show ((5823 / 5000) : ℝ) = ((5000 / 5823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2002_neg : (89922313 / 500000000) ≤ -Real.log (4177 / 5000) ∧
    -Real.log (4177 / 5000) ≤ (179844627 / 1000000000) := by
  have h := checkLog_sound (w := (823 / 9177)) (n := 12)
    (lo := (89922313 / 500000000)) (hi := (179844627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4177) = 1/(4177 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2002 : Bounds (-179844627 / 1000000000) (-89922313 / 500000000) (Real.log (4177 / 5000)) := by
  have h := reflection_log_2002_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2003_neg : (82293 / 500000000) ≤ -Real.log (5000000 / 5000823) ∧
    -Real.log (5000000 / 5000823) ≤ (164587 / 1000000000) := by
  have h := checkLog_sound (w := (823 / 10000823)) (n := 12)
    (lo := (82293 / 500000000)) (hi := (164587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000823 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000823 / 5000000) = 1/(5000000 / 5000823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2003 : Bounds (82293 / 500000000) (164587 / 1000000000) (Real.log (5000823 / 5000000)) := by
  have h := reflection_log_2003_neg
  have he : Real.log (5000823 / 5000000) = -Real.log (5000000 / 5000823) := by
    rw [show ((5000823 / 5000000) : ℝ) = ((5000000 / 5000823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2004_neg : (164613 / 1000000000) ≤ -Real.log (4999177 / 5000000) ∧
    -Real.log (4999177 / 5000000) ≤ (82307 / 500000000) := by
  have h := checkLog_sound (w := (823 / 9999177)) (n := 12)
    (lo := (164613 / 1000000000)) (hi := (82307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999177) = 1/(4999177 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2004 : Bounds (-82307 / 500000000) (-164613 / 1000000000) (Real.log (4999177 / 5000000)) := by
  have h := reflection_log_2004_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2005_neg : (79339691 / 1000000000) ≤ -Real.log (250000 / 270643) ∧
    -Real.log (250000 / 270643) ≤ (19834923 / 250000000) := by
  have h := checkLog_sound (w := (20643 / 520643)) (n := 12)
    (lo := (79339691 / 1000000000)) (hi := (19834923 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270643 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270643 / 250000) = 1/(250000 / 270643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2005 : Bounds (79339691 / 1000000000) (19834923 / 250000000) (Real.log (270643 / 250000)) := by
  have h := reflection_log_2005_neg
  have he : Real.log (270643 / 250000) = -Real.log (250000 / 270643) := by
    rw [show ((270643 / 250000) : ℝ) = ((250000 / 270643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2006_neg : (10772647 / 125000000) ≤ -Real.log (229357 / 250000) ∧
    -Real.log (229357 / 250000) ≤ (86181177 / 1000000000) := by
  have h := checkLog_sound (w := (20643 / 479357)) (n := 12)
    (lo := (10772647 / 125000000)) (hi := (86181177 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229357) = 1/(229357 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2006 : Bounds (-86181177 / 1000000000) (-10772647 / 125000000) (Real.log (229357 / 250000)) := by
  have h := reflection_log_2006_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2007_neg : (19884799 / 250000000) ≤ -Real.log (250000 / 270697) ∧
    -Real.log (250000 / 270697) ≤ (79539197 / 1000000000) := by
  have h := checkLog_sound (w := (20697 / 520697)) (n := 12)
    (lo := (19884799 / 250000000)) (hi := (79539197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270697 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270697 / 250000) = 1/(250000 / 270697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2007 : Bounds (19884799 / 250000000) (79539197 / 1000000000) (Real.log (270697 / 250000)) := by
  have h := reflection_log_2007_neg
  have he : Real.log (270697 / 250000) = -Real.log (250000 / 270697) := by
    rw [show ((270697 / 250000) : ℝ) = ((250000 / 270697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2008_neg : (21604161 / 250000000) ≤ -Real.log (229303 / 250000) ∧
    -Real.log (229303 / 250000) ≤ (17283329 / 200000000) := by
  have h := checkLog_sound (w := (20697 / 479303)) (n := 12)
    (lo := (21604161 / 250000000)) (hi := (17283329 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229303) = 1/(229303 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2008 : Bounds (-17283329 / 200000000) (-21604161 / 250000000) (Real.log (229303 / 250000)) := by
  have h := reflection_log_2008_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2009_neg : (859681 / 125000000) ≤ -Real.log (62071634191 / 62500000000) ∧
    -Real.log (62071634191 / 62500000000) ≤ (6877449 / 1000000000) := by
  have h := checkLog_sound (w := (428365809 / 124571634191)) (n := 12)
    (lo := (859681 / 125000000)) (hi := (6877449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62071634191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62071634191) = 1/(62071634191 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2009 : Bounds (-6877449 / 1000000000) (-859681 / 125000000) (Real.log (62071634191 / 62500000000)) := by
  have h := reflection_log_2009_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2010_neg : (1710371 / 250000000) ≤ -Real.log (62073866551 / 62500000000) ∧
    -Real.log (62073866551 / 62500000000) ≤ (1368297 / 200000000) := by
  have h := checkLog_sound (w := (426133449 / 124573866551)) (n := 12)
    (lo := (1710371 / 250000000)) (hi := (1368297 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62073866551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62073866551) = 1/(62073866551 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2010 : Bounds (-1368297 / 200000000) (-1710371 / 250000000) (Real.log (62073866551 / 62500000000)) := by
  have h := reflection_log_2010_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2011_neg : (165520867 / 1000000000) ≤ -Real.log (500000000000 / 590003793213) ∧
    -Real.log (500000000000 / 590003793213) ≤ (41380217 / 250000000) := by
  have h := checkLog_sound (w := (90003793213 / 1090003793213)) (n := 12)
    (lo := (165520867 / 1000000000)) (hi := (41380217 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590003793213 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590003793213 / 500000000000) = 1/(500000000000 / 590003793213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2011 : Bounds (165520867 / 1000000000) (41380217 / 250000000) (Real.log (590003793213 / 500000000000)) := by
  have h := reflection_log_2011_neg
  have he : Real.log (590003793213 / 500000000000) = -Real.log (500000000000 / 590003793213) := by
    rw [show ((590003793213 / 500000000000) : ℝ) = ((500000000000 / 590003793213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2012_neg : (165955841 / 1000000000) ≤ -Real.log (125000000000 / 147565121259) ∧
    -Real.log (125000000000 / 147565121259) ≤ (82977921 / 500000000) := by
  have h := checkLog_sound (w := (22565121259 / 272565121259)) (n := 12)
    (lo := (165955841 / 1000000000)) (hi := (82977921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147565121259 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147565121259 / 125000000000) = 1/(125000000000 / 147565121259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2012 : Bounds (165955841 / 1000000000) (82977921 / 500000000) (Real.log (147565121259 / 125000000000)) := by
  have h := reflection_log_2012_neg
  have he : Real.log (147565121259 / 125000000000) = -Real.log (125000000000 / 147565121259) := by
    rw [show ((147565121259 / 125000000000) : ℝ) = ((125000000000 / 147565121259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2013_neg : (332016741 / 1000000000) ≤ -Real.log (500000000000 / 696888090963) ∧
    -Real.log (500000000000 / 696888090963) ≤ (166008371 / 500000000) := by
  have h := checkLog_sound (w := (196888090963 / 1196888090963)) (n := 12)
    (lo := (332016741 / 1000000000)) (hi := (166008371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696888090963 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696888090963 / 500000000000) = 1/(500000000000 / 696888090963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2013 : Bounds (332016741 / 1000000000) (166008371 / 500000000) (Real.log (696888090963 / 500000000000)) := by
  have h := reflection_log_2013_neg
  have he : Real.log (696888090963 / 500000000000) = -Real.log (500000000000 / 696888090963) := by
    rw [show ((696888090963 / 500000000000) : ℝ) = ((500000000000 / 696888090963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2014_neg : (332222307 / 1000000000) ≤ -Real.log (250000000000 / 348515681111) ∧
    -Real.log (250000000000 / 348515681111) ≤ (83055577 / 250000000) := by
  have h := checkLog_sound (w := (98515681111 / 598515681111)) (n := 12)
    (lo := (332222307 / 1000000000)) (hi := (83055577 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((348515681111 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(348515681111 / 250000000000) = 1/(250000000000 / 348515681111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2014 : Bounds (332222307 / 1000000000) (83055577 / 250000000) (Real.log (348515681111 / 250000000000)) := by
  have h := reflection_log_2014_neg
  have he : Real.log (348515681111 / 250000000000) = -Real.log (250000000000 / 348515681111) := by
    rw [show ((348515681111 / 250000000000) : ℝ) = ((250000000000 / 348515681111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2015_neg : (152463543 / 1000000000) ≤ -Real.log (10000 / 11647) ∧
    -Real.log (10000 / 11647) ≤ (19057943 / 125000000) := by
  have h := checkLog_sound (w := (1647 / 21647)) (n := 12)
    (lo := (152463543 / 1000000000)) (hi := (19057943 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11647 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11647 / 10000) = 1/(10000 / 11647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2015 : Bounds (152463543 / 1000000000) (19057943 / 125000000) (Real.log (11647 / 10000)) := by
  have h := reflection_log_2015_neg
  have he : Real.log (11647 / 10000) = -Real.log (10000 / 11647) := by
    rw [show ((11647 / 10000) : ℝ) = ((10000 / 11647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2016_neg : (179964337 / 1000000000) ≤ -Real.log (8353 / 10000) ∧
    -Real.log (8353 / 10000) ≤ (89982169 / 500000000) := by
  have h := checkLog_sound (w := (1647 / 18353)) (n := 12)
    (lo := (179964337 / 1000000000)) (hi := (89982169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8353) = 1/(8353 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2016 : Bounds (-89982169 / 500000000) (-179964337 / 1000000000) (Real.log (8353 / 10000)) := by
  have h := reflection_log_2016_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2017_neg : (82343 / 500000000) ≤ -Real.log (10000000 / 10001647) ∧
    -Real.log (10000000 / 10001647) ≤ (164687 / 1000000000) := by
  have h := checkLog_sound (w := (1647 / 20001647)) (n := 12)
    (lo := (82343 / 500000000)) (hi := (164687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001647 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001647 / 10000000) = 1/(10000000 / 10001647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2017 : Bounds (82343 / 500000000) (164687 / 1000000000) (Real.log (10001647 / 10000000)) := by
  have h := reflection_log_2017_neg
  have he : Real.log (10001647 / 10000000) = -Real.log (10000000 / 10001647) := by
    rw [show ((10001647 / 10000000) : ℝ) = ((10000000 / 10001647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2018_neg : (164713 / 1000000000) ≤ -Real.log (9998353 / 10000000) ∧
    -Real.log (9998353 / 10000000) ≤ (82357 / 500000000) := by
  have h := checkLog_sound (w := (1647 / 19998353)) (n := 12)
    (lo := (164713 / 1000000000)) (hi := (82357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998353) = 1/(9998353 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2018 : Bounds (-82357 / 500000000) (-164713 / 1000000000) (Real.log (9998353 / 10000000)) := by
  have h := reflection_log_2018_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2019_neg : (198467 / 2500000) ≤ -Real.log (1000000 / 1082623) ∧
    -Real.log (1000000 / 1082623) ≤ (79386801 / 1000000000) := by
  have h := checkLog_sound (w := (82623 / 2082623)) (n := 12)
    (lo := (198467 / 2500000)) (hi := (79386801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082623 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082623 / 1000000) = 1/(1000000 / 1082623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2019 : Bounds (198467 / 2500000) (79386801 / 1000000000) (Real.log (1082623 / 1000000)) := by
  have h := reflection_log_2019_neg
  have he : Real.log (1082623 / 1000000) = -Real.log (1000000 / 1082623) := by
    rw [show ((1082623 / 1000000) : ℝ) = ((1000000 / 1082623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2020_neg : (86236767 / 1000000000) ≤ -Real.log (917377 / 1000000) ∧
    -Real.log (917377 / 1000000) ≤ (2694899 / 31250000) := by
  have h := checkLog_sound (w := (82623 / 1917377)) (n := 12)
    (lo := (86236767 / 1000000000)) (hi := (2694899 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917377) = 1/(917377 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2020 : Bounds (-2694899 / 31250000) (-86236767 / 1000000000) (Real.log (917377 / 1000000)) := by
  have h := reflection_log_2020_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2021_neg : (15917259 / 200000000) ≤ -Real.log (1000000 / 1082839) ∧
    -Real.log (1000000 / 1082839) ≤ (9948287 / 125000000) := by
  have h := checkLog_sound (w := (82839 / 2082839)) (n := 12)
    (lo := (15917259 / 200000000)) (hi := (9948287 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082839 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082839 / 1000000) = 1/(1000000 / 1082839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2021 : Bounds (15917259 / 200000000) (9948287 / 125000000) (Real.log (1082839 / 1000000)) := by
  have h := reflection_log_2021_neg
  have he : Real.log (1082839 / 1000000) = -Real.log (1000000 / 1082839) := by
    rw [show ((1082839 / 1000000) : ℝ) = ((1000000 / 1082839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2022_neg : (86472249 / 1000000000) ≤ -Real.log (917161 / 1000000) ∧
    -Real.log (917161 / 1000000) ≤ (345889 / 4000000) := by
  have h := checkLog_sound (w := (82839 / 1917161)) (n := 12)
    (lo := (86472249 / 1000000000)) (hi := (345889 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917161) = 1/(917161 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2022 : Bounds (-345889 / 4000000) (-86472249 / 1000000000) (Real.log (917161 / 1000000)) := by
  have h := reflection_log_2022_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2023_neg : (6885953 / 1000000000) ≤ -Real.log (993137700079 / 1000000000000) ∧
    -Real.log (993137700079 / 1000000000000) ≤ (3442977 / 500000000) := by
  have h := checkLog_sound (w := (6862299921 / 1993137700079)) (n := 12)
    (lo := (6885953 / 1000000000)) (hi := (3442977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993137700079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993137700079) = 1/(993137700079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2023 : Bounds (-3442977 / 500000000) (-6885953 / 1000000000) (Real.log (993137700079 / 1000000000000)) := by
  have h := reflection_log_2023_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2024_neg : (6849967 / 1000000000) ≤ -Real.log (993173439871 / 1000000000000) ∧
    -Real.log (993173439871 / 1000000000000) ≤ (428123 / 62500000) := by
  have h := checkLog_sound (w := (6826560129 / 1993173439871)) (n := 12)
    (lo := (6849967 / 1000000000)) (hi := (428123 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993173439871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993173439871) = 1/(993173439871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2024 : Bounds (-428123 / 62500000) (-6849967 / 1000000000) (Real.log (993173439871 / 1000000000000)) := by
  have h := reflection_log_2024_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2025_neg : (10351473 / 62500000) ≤ -Real.log (500000000000 / 590064390103) ∧
    -Real.log (500000000000 / 590064390103) ≤ (165623569 / 1000000000) := by
  have h := checkLog_sound (w := (90064390103 / 1090064390103)) (n := 12)
    (lo := (10351473 / 62500000)) (hi := (165623569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590064390103 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590064390103 / 500000000000) = 1/(500000000000 / 590064390103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2025 : Bounds (10351473 / 62500000) (165623569 / 1000000000) (Real.log (590064390103 / 500000000000)) := by
  have h := reflection_log_2025_neg
  have he : Real.log (590064390103 / 500000000000) = -Real.log (500000000000 / 590064390103) := by
    rw [show ((590064390103 / 500000000000) : ℝ) = ((500000000000 / 590064390103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2026_neg : (33211709 / 200000000) ≤ -Real.log (500000000000 / 590321110471) ∧
    -Real.log (500000000000 / 590321110471) ≤ (83029273 / 500000000) := by
  have h := checkLog_sound (w := (90321110471 / 1090321110471)) (n := 12)
    (lo := (33211709 / 200000000)) (hi := (83029273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590321110471 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590321110471 / 500000000000) = 1/(500000000000 / 590321110471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2026 : Bounds (33211709 / 200000000) (83029273 / 500000000) (Real.log (590321110471 / 500000000000)) := by
  have h := reflection_log_2026_neg
  have he : Real.log (590321110471 / 500000000000) = -Real.log (500000000000 / 590321110471) := by
    rw [show ((590321110471 / 500000000000) : ℝ) = ((500000000000 / 590321110471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2027_neg : (332222307 / 1000000000) ≤ -Real.log (500000000000 / 697031362221) ∧
    -Real.log (500000000000 / 697031362221) ≤ (83055577 / 250000000) := by
  have h := checkLog_sound (w := (197031362221 / 1197031362221)) (n := 12)
    (lo := (332222307 / 1000000000)) (hi := (83055577 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697031362221 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697031362221 / 500000000000) = 1/(500000000000 / 697031362221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2027 : Bounds (332222307 / 1000000000) (83055577 / 250000000) (Real.log (697031362221 / 500000000000)) := by
  have h := reflection_log_2027_neg
  have he : Real.log (697031362221 / 500000000000) = -Real.log (500000000000 / 697031362221) := by
    rw [show ((697031362221 / 500000000000) : ℝ) = ((500000000000 / 697031362221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2028_neg : (8310697 / 25000000) ≤ -Real.log (100000000000 / 139434933557) ∧
    -Real.log (100000000000 / 139434933557) ≤ (332427881 / 1000000000) := by
  have h := checkLog_sound (w := (39434933557 / 239434933557)) (n := 12)
    (lo := (8310697 / 25000000)) (hi := (332427881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((139434933557 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(139434933557 / 100000000000) = 1/(100000000000 / 139434933557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2028 : Bounds (8310697 / 25000000) (332427881 / 1000000000) (Real.log (139434933557 / 100000000000)) := by
  have h := reflection_log_2028_neg
  have he : Real.log (139434933557 / 100000000000) = -Real.log (100000000000 / 139434933557) := by
    rw [show ((139434933557 / 100000000000) : ℝ) = ((100000000000 / 139434933557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2029_neg : (76274699 / 500000000) ≤ -Real.log (625 / 728) ∧
    -Real.log (625 / 728) ≤ (152549399 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 1353)) (n := 12)
    (lo := (76274699 / 500000000)) (hi := (152549399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((728 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(728 / 625) = 1/(625 / 728) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2029 : Bounds (76274699 / 500000000) (152549399 / 1000000000) (Real.log (728 / 625)) := by
  have h := reflection_log_2029_neg
  have he : Real.log (728 / 625) = -Real.log (625 / 728) := by
    rw [show ((728 / 625) : ℝ) = ((625 / 728) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2030_neg : (180084061 / 1000000000) ≤ -Real.log (522 / 625) ∧
    -Real.log (522 / 625) ≤ (90042031 / 500000000) := by
  have h := checkLog_sound (w := (103 / 1147)) (n := 12)
    (lo := (180084061 / 1000000000)) (hi := (90042031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 522) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 522) = 1/(522 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2030 : Bounds (-90042031 / 500000000) (-180084061 / 1000000000) (Real.log (522 / 625)) := by
  have h := reflection_log_2030_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2031_neg : (82393 / 500000000) ≤ -Real.log (625000 / 625103) ∧
    -Real.log (625000 / 625103) ≤ (164787 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 1250103)) (n := 12)
    (lo := (82393 / 500000000)) (hi := (164787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625103 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625103 / 625000) = 1/(625000 / 625103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2031 : Bounds (82393 / 500000000) (164787 / 1000000000) (Real.log (625103 / 625000)) := by
  have h := reflection_log_2031_neg
  have he : Real.log (625103 / 625000) = -Real.log (625000 / 625103) := by
    rw [show ((625103 / 625000) : ℝ) = ((625000 / 625103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2032_neg : (164813 / 1000000000) ≤ -Real.log (624897 / 625000) ∧
    -Real.log (624897 / 625000) ≤ (82407 / 500000000) := by
  have h := checkLog_sound (w := (103 / 1249897)) (n := 12)
    (lo := (164813 / 1000000000)) (hi := (82407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624897) = 1/(624897 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2032 : Bounds (-82407 / 500000000) (-164813 / 1000000000) (Real.log (624897 / 625000)) := by
  have h := reflection_log_2032_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2033_neg : (79433907 / 1000000000) ≤ -Real.log (500000 / 541337) ∧
    -Real.log (500000 / 541337) ≤ (19858477 / 250000000) := by
  have h := checkLog_sound (w := (41337 / 1041337)) (n := 12)
    (lo := (79433907 / 1000000000)) (hi := (19858477 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541337 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541337 / 500000) = 1/(500000 / 541337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2033 : Bounds (79433907 / 1000000000) (19858477 / 250000000) (Real.log (541337 / 500000)) := by
  have h := reflection_log_2033_neg
  have he : Real.log (541337 / 500000) = -Real.log (500000 / 541337) := by
    rw [show ((541337 / 500000) : ℝ) = ((500000 / 541337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2034_neg : (43146181 / 500000000) ≤ -Real.log (458663 / 500000) ∧
    -Real.log (458663 / 500000) ≤ (86292363 / 1000000000) := by
  have h := checkLog_sound (w := (41337 / 958663)) (n := 12)
    (lo := (43146181 / 500000000)) (hi := (86292363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458663) = 1/(458663 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2034 : Bounds (-86292363 / 1000000000) (-43146181 / 500000000) (Real.log (458663 / 500000)) := by
  have h := reflection_log_2034_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2035_neg : (79632469 / 1000000000) ≤ -Real.log (1000000 / 1082889) ∧
    -Real.log (1000000 / 1082889) ≤ (7963247 / 100000000) := by
  have h := checkLog_sound (w := (82889 / 2082889)) (n := 12)
    (lo := (79632469 / 1000000000)) (hi := (7963247 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082889 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082889 / 1000000) = 1/(1000000 / 1082889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2035 : Bounds (79632469 / 1000000000) (7963247 / 100000000) (Real.log (1082889 / 1000000)) := by
  have h := reflection_log_2035_neg
  have he : Real.log (1082889 / 1000000) = -Real.log (1000000 / 1082889) := by
    rw [show ((1082889 / 1000000) : ℝ) = ((1000000 / 1082889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2036_neg : (86526767 / 1000000000) ≤ -Real.log (917111 / 1000000) ∧
    -Real.log (917111 / 1000000) ≤ (5407923 / 62500000) := by
  have h := checkLog_sound (w := (82889 / 1917111)) (n := 12)
    (lo := (86526767 / 1000000000)) (hi := (5407923 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917111) = 1/(917111 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2036 : Bounds (-5407923 / 62500000) (-86526767 / 1000000000) (Real.log (917111 / 1000000)) := by
  have h := reflection_log_2036_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2037_neg : (6894297 / 1000000000) ≤ -Real.log (993129413679 / 1000000000000) ∧
    -Real.log (993129413679 / 1000000000000) ≤ (3447149 / 500000000) := by
  have h := checkLog_sound (w := (6870586321 / 1993129413679)) (n := 12)
    (lo := (6894297 / 1000000000)) (hi := (3447149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993129413679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993129413679) = 1/(993129413679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2037 : Bounds (-3447149 / 500000000) (-6894297 / 1000000000) (Real.log (993129413679 / 1000000000000)) := by
  have h := reflection_log_2037_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2038_neg : (1371691 / 200000000) ≤ -Real.log (248291252431 / 250000000000) ∧
    -Real.log (248291252431 / 250000000000) ≤ (857307 / 125000000) := by
  have h := checkLog_sound (w := (1708747569 / 498291252431)) (n := 12)
    (lo := (1371691 / 200000000)) (hi := (857307 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248291252431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248291252431) = 1/(248291252431 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2038 : Bounds (-857307 / 125000000) (-1371691 / 200000000) (Real.log (248291252431 / 250000000000)) := by
  have h := reflection_log_2038_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2039_neg : (165726269 / 1000000000) ≤ -Real.log (500000000000 / 590124993731) ∧
    -Real.log (500000000000 / 590124993731) ≤ (16572627 / 100000000) := by
  have h := checkLog_sound (w := (90124993731 / 1090124993731)) (n := 12)
    (lo := (165726269 / 1000000000)) (hi := (16572627 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590124993731 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590124993731 / 500000000000) = 1/(500000000000 / 590124993731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2039 : Bounds (165726269 / 1000000000) (16572627 / 100000000) (Real.log (590124993731 / 500000000000)) := by
  have h := reflection_log_2039_neg
  have he : Real.log (590124993731 / 500000000000) = -Real.log (500000000000 / 590124993731) := by
    rw [show ((590124993731 / 500000000000) : ℝ) = ((500000000000 / 590124993731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2040_neg : (41539809 / 250000000) ≤ -Real.log (250000000000 / 295190276859) ∧
    -Real.log (250000000000 / 295190276859) ≤ (166159237 / 1000000000) := by
  have h := checkLog_sound (w := (45190276859 / 545190276859)) (n := 12)
    (lo := (41539809 / 250000000)) (hi := (166159237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295190276859 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295190276859 / 250000000000) = 1/(250000000000 / 295190276859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2040 : Bounds (41539809 / 250000000) (166159237 / 1000000000) (Real.log (295190276859 / 250000000000)) := by
  have h := reflection_log_2040_neg
  have he : Real.log (295190276859 / 250000000000) = -Real.log (250000000000 / 295190276859) := by
    rw [show ((295190276859 / 250000000000) : ℝ) = ((250000000000 / 295190276859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2041_neg : (8310697 / 25000000) ≤ -Real.log (62500000000 / 87146833473) ∧
    -Real.log (62500000000 / 87146833473) ≤ (332427881 / 1000000000) := by
  have h := checkLog_sound (w := (24646833473 / 149646833473)) (n := 12)
    (lo := (8310697 / 25000000)) (hi := (332427881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87146833473 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87146833473 / 62500000000) = 1/(62500000000 / 87146833473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2041 : Bounds (8310697 / 25000000) (332427881 / 1000000000) (Real.log (87146833473 / 62500000000)) := by
  have h := reflection_log_2041_neg
  have he : Real.log (87146833473 / 62500000000) = -Real.log (62500000000 / 87146833473) := by
    rw [show ((87146833473 / 62500000000) : ℝ) = ((62500000000 / 87146833473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2042_neg : (16631673 / 50000000) ≤ -Real.log (500000000000 / 697318007663) ∧
    -Real.log (500000000000 / 697318007663) ≤ (332633461 / 1000000000) := by
  have h := checkLog_sound (w := (197318007663 / 1197318007663)) (n := 12)
    (lo := (16631673 / 50000000)) (hi := (332633461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((697318007663 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(697318007663 / 500000000000) = 1/(500000000000 / 697318007663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2042 : Bounds (16631673 / 50000000) (332633461 / 1000000000) (Real.log (697318007663 / 500000000000)) := by
  have h := reflection_log_2042_neg
  have he : Real.log (697318007663 / 500000000000) = -Real.log (500000000000 / 697318007663) := by
    rw [show ((697318007663 / 500000000000) : ℝ) = ((500000000000 / 697318007663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2043_neg : (76317623 / 500000000) ≤ -Real.log (10000 / 11649) ∧
    -Real.log (10000 / 11649) ≤ (152635247 / 1000000000) := by
  have h := checkLog_sound (w := (1649 / 21649)) (n := 12)
    (lo := (76317623 / 500000000)) (hi := (152635247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11649 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11649 / 10000) = 1/(10000 / 11649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2043 : Bounds (76317623 / 500000000) (152635247 / 1000000000) (Real.log (11649 / 10000)) := by
  have h := reflection_log_2043_neg
  have he : Real.log (11649 / 10000) = -Real.log (10000 / 11649) := by
    rw [show ((11649 / 10000) : ℝ) = ((10000 / 11649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2044_neg : (901019 / 5000000) ≤ -Real.log (8351 / 10000) ∧
    -Real.log (8351 / 10000) ≤ (180203801 / 1000000000) := by
  have h := checkLog_sound (w := (1649 / 18351)) (n := 12)
    (lo := (901019 / 5000000)) (hi := (180203801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8351) = 1/(8351 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2044 : Bounds (-180203801 / 1000000000) (-901019 / 5000000) (Real.log (8351 / 10000)) := by
  have h := reflection_log_2044_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2045_neg : (82443 / 500000000) ≤ -Real.log (10000000 / 10001649) ∧
    -Real.log (10000000 / 10001649) ≤ (164887 / 1000000000) := by
  have h := checkLog_sound (w := (1649 / 20001649)) (n := 12)
    (lo := (82443 / 500000000)) (hi := (164887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001649 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001649 / 10000000) = 1/(10000000 / 10001649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2045 : Bounds (82443 / 500000000) (164887 / 1000000000) (Real.log (10001649 / 10000000)) := by
  have h := reflection_log_2045_neg
  have he : Real.log (10001649 / 10000000) = -Real.log (10000000 / 10001649) := by
    rw [show ((10001649 / 10000000) : ℝ) = ((10000000 / 10001649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2046_neg : (164913 / 1000000000) ≤ -Real.log (9998351 / 10000000) ∧
    -Real.log (9998351 / 10000000) ≤ (82457 / 500000000) := by
  have h := checkLog_sound (w := (1649 / 19998351)) (n := 12)
    (lo := (164913 / 1000000000)) (hi := (82457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998351) = 1/(9998351 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2046 : Bounds (-82457 / 500000000) (-164913 / 1000000000) (Real.log (9998351 / 10000000)) := by
  have h := reflection_log_2046_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2047_neg : (79480087 / 1000000000) ≤ -Real.log (250000 / 270681) ∧
    -Real.log (250000 / 270681) ≤ (9935011 / 125000000) := by
  have h := checkLog_sound (w := (20681 / 520681)) (n := 12)
    (lo := (79480087 / 1000000000)) (hi := (9935011 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270681 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270681 / 250000) = 1/(250000 / 270681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2047 : Bounds (79480087 / 1000000000) (9935011 / 125000000) (Real.log (270681 / 250000)) := by
  have h := reflection_log_2047_neg
  have he : Real.log (270681 / 250000) = -Real.log (250000 / 270681) := by
    rw [show ((270681 / 250000) : ℝ) = ((250000 / 270681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
