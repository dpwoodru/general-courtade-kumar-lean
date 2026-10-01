import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_6848_neg : (47732811 / 500000000) ≤ -Real.log (1000000 / 1100171) ∧
    -Real.log (1000000 / 1100171) ≤ (95465623 / 1000000000) := by
  have h := checkLog_sound (w := (100171 / 2100171)) (n := 12)
    (lo := (47732811 / 500000000)) (hi := (95465623 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1100171 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1100171 / 1000000) = 1/(1000000 / 1100171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6848 : Bounds (47732811 / 500000000) (95465623 / 1000000000) (Real.log (1100171 / 1000000)) := by
  have h := reflection_log_6848_neg
  have he : Real.log (1100171 / 1000000) = -Real.log (1000000 / 1100171) := by
    rw [show ((1100171 / 1000000) : ℝ) = ((1000000 / 1100171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6849_neg : (105550533 / 1000000000) ≤ -Real.log (899829 / 1000000) ∧
    -Real.log (899829 / 1000000) ≤ (52775267 / 500000000) := by
  have h := checkLog_sound (w := (100171 / 1899829)) (n := 12)
    (lo := (105550533 / 1000000000)) (hi := (52775267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 899829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 899829) = 1/(899829 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6849 : Bounds (-52775267 / 500000000) (-105550533 / 1000000000) (Real.log (899829 / 1000000)) := by
  have h := reflection_log_6849_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6850_neg : (3827677 / 40000000) ≤ -Real.log (50000 / 55021) ∧
    -Real.log (50000 / 55021) ≤ (47845963 / 500000000) := by
  have h := checkLog_sound (w := (5021 / 105021)) (n := 12)
    (lo := (3827677 / 40000000)) (hi := (47845963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55021 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55021 / 50000) = 1/(50000 / 55021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6850 : Bounds (3827677 / 40000000) (47845963 / 500000000) (Real.log (55021 / 50000)) := by
  have h := reflection_log_6850_neg
  have he : Real.log (55021 / 50000) = -Real.log (50000 / 55021) := by
    rw [show ((55021 / 50000) : ℝ) = ((50000 / 55021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6851_neg : (105827291 / 1000000000) ≤ -Real.log (44979 / 50000) ∧
    -Real.log (44979 / 50000) ≤ (26456823 / 250000000) := by
  have h := checkLog_sound (w := (5021 / 94979)) (n := 12)
    (lo := (105827291 / 1000000000)) (hi := (26456823 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 44979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 44979) = 1/(44979 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6851 : Bounds (-26456823 / 250000000) (-105827291 / 1000000000) (Real.log (44979 / 50000)) := by
  have h := reflection_log_6851_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6852_neg : (5067683 / 500000000) ≤ -Real.log (2474789559 / 2500000000) ∧
    -Real.log (2474789559 / 2500000000) ≤ (10135367 / 1000000000) := by
  have h := checkLog_sound (w := (25210441 / 4974789559)) (n := 12)
    (lo := (5067683 / 500000000)) (hi := (10135367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2474789559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2474789559) = 1/(2474789559 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6852 : Bounds (-10135367 / 1000000000) (-5067683 / 500000000) (Real.log (2474789559 / 2500000000)) := by
  have h := reflection_log_6852_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6853_neg : (10084911 / 1000000000) ≤ -Real.log (989965770759 / 1000000000000) ∧
    -Real.log (989965770759 / 1000000000000) ≤ (630307 / 62500000) := by
  have h := checkLog_sound (w := (10034229241 / 1989965770759)) (n := 12)
    (lo := (10084911 / 1000000000)) (hi := (630307 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989965770759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989965770759) = 1/(989965770759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6853 : Bounds (-630307 / 62500000) (-10084911 / 1000000000) (Real.log (989965770759 / 1000000000000)) := by
  have h := reflection_log_6853_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6854_neg : (40203231 / 200000000) ≤ -Real.log (25000000000 / 30566113117) ∧
    -Real.log (25000000000 / 30566113117) ≤ (50254039 / 250000000) := by
  have h := checkLog_sound (w := (5566113117 / 55566113117)) (n := 12)
    (lo := (40203231 / 200000000)) (hi := (50254039 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30566113117 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30566113117 / 25000000000) = 1/(25000000000 / 30566113117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6854 : Bounds (40203231 / 200000000) (50254039 / 250000000) (Real.log (30566113117 / 25000000000)) := by
  have h := reflection_log_6854_neg
  have he : Real.log (30566113117 / 25000000000) = -Real.log (25000000000 / 30566113117) := by
    rw [show ((30566113117 / 25000000000) : ℝ) = ((25000000000 / 30566113117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6855_neg : (12594951 / 62500000) ≤ -Real.log (250000000000 / 305814935859) ∧
    -Real.log (250000000000 / 305814935859) ≤ (201519217 / 1000000000) := by
  have h := checkLog_sound (w := (55814935859 / 555814935859)) (n := 12)
    (lo := (12594951 / 62500000)) (hi := (201519217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305814935859 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305814935859 / 250000000000) = 1/(250000000000 / 305814935859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6855 : Bounds (12594951 / 62500000) (201519217 / 1000000000) (Real.log (305814935859 / 250000000000)) := by
  have h := reflection_log_6855_neg
  have he : Real.log (305814935859 / 250000000000) = -Real.log (250000000000 / 305814935859) := by
    rw [show ((305814935859 / 250000000000) : ℝ) = ((250000000000 / 305814935859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6856_neg : (403590459 / 1000000000) ≤ -Real.log (500000000000 / 748595330253) ∧
    -Real.log (500000000000 / 748595330253) ≤ (20179523 / 50000000) := by
  have h := checkLog_sound (w := (248595330253 / 1248595330253)) (n := 12)
    (lo := (403590459 / 1000000000)) (hi := (20179523 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((748595330253 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(748595330253 / 500000000000) = 1/(500000000000 / 748595330253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6856 : Bounds (403590459 / 1000000000) (20179523 / 50000000) (Real.log (748595330253 / 500000000000)) := by
  have h := reflection_log_6856_neg
  have he : Real.log (748595330253 / 500000000000) = -Real.log (500000000000 / 748595330253) := by
    rw [show ((748595330253 / 500000000000) : ℝ) = ((500000000000 / 748595330253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6857_neg : (201899359 / 500000000) ≤ -Real.log (31250000000 / 46796953047) ∧
    -Real.log (31250000000 / 46796953047) ≤ (403798719 / 1000000000) := by
  have h := checkLog_sound (w := (15546953047 / 78046953047)) (n := 12)
    (lo := (201899359 / 500000000)) (hi := (403798719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46796953047 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46796953047 / 31250000000) = 1/(31250000000 / 46796953047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6857 : Bounds (201899359 / 500000000) (403798719 / 1000000000) (Real.log (46796953047 / 31250000000)) := by
  have h := reflection_log_6857_neg
  have he : Real.log (46796953047 / 31250000000) = -Real.log (31250000000 / 46796953047) := by
    rw [show ((46796953047 / 31250000000) : ℝ) = ((31250000000 / 46796953047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6858_neg : (181738053 / 1000000000) ≤ -Real.log (10000 / 11993) ∧
    -Real.log (10000 / 11993) ≤ (90869027 / 500000000) := by
  have h := checkLog_sound (w := (1993 / 21993)) (n := 12)
    (lo := (181738053 / 1000000000)) (hi := (90869027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11993 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11993 / 10000) = 1/(10000 / 11993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6858 : Bounds (181738053 / 1000000000) (90869027 / 500000000) (Real.log (11993 / 10000)) := by
  have h := reflection_log_6858_neg
  have he : Real.log (11993 / 10000) = -Real.log (10000 / 11993) := by
    rw [show ((11993 / 10000) : ℝ) = ((10000 / 11993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6859_neg : (222268933 / 1000000000) ≤ -Real.log (8007 / 10000) ∧
    -Real.log (8007 / 10000) ≤ (111134467 / 500000000) := by
  have h := checkLog_sound (w := (1993 / 18007)) (n := 12)
    (lo := (222268933 / 1000000000)) (hi := (111134467 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8007) = 1/(8007 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6859 : Bounds (-111134467 / 500000000) (-222268933 / 1000000000) (Real.log (8007 / 10000)) := by
  have h := reflection_log_6859_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6860_neg : (2491 / 12500000) ≤ -Real.log (10000000 / 10001993) ∧
    -Real.log (10000000 / 10001993) ≤ (199281 / 1000000000) := by
  have h := checkLog_sound (w := (1993 / 20001993)) (n := 12)
    (lo := (2491 / 12500000)) (hi := (199281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001993 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001993 / 10000000) = 1/(10000000 / 10001993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6860 : Bounds (2491 / 12500000) (199281 / 1000000000) (Real.log (10001993 / 10000000)) := by
  have h := reflection_log_6860_neg
  have he : Real.log (10001993 / 10000000) = -Real.log (10000000 / 10001993) := by
    rw [show ((10001993 / 10000000) : ℝ) = ((10000000 / 10001993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6861_neg : (199319 / 1000000000) ≤ -Real.log (9998007 / 10000000) ∧
    -Real.log (9998007 / 10000000) ≤ (4983 / 25000000) := by
  have h := checkLog_sound (w := (1993 / 19998007)) (n := 12)
    (lo := (199319 / 1000000000)) (hi := (4983 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998007) = 1/(9998007 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6861 : Bounds (-4983 / 25000000) (-199319 / 1000000000) (Real.log (9998007 / 10000000)) := by
  have h := reflection_log_6861_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6862_neg : (95511977 / 1000000000) ≤ -Real.log (500000 / 550111) ∧
    -Real.log (500000 / 550111) ≤ (47755989 / 500000000) := by
  have h := checkLog_sound (w := (50111 / 1050111)) (n := 12)
    (lo := (95511977 / 1000000000)) (hi := (47755989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((550111 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(550111 / 500000) = 1/(500000 / 550111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6862 : Bounds (95511977 / 1000000000) (47755989 / 500000000) (Real.log (550111 / 500000)) := by
  have h := reflection_log_6862_neg
  have he : Real.log (550111 / 500000) = -Real.log (500000 / 550111) := by
    rw [show ((550111 / 500000) : ℝ) = ((500000 / 550111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6863_neg : (26401803 / 250000000) ≤ -Real.log (449889 / 500000) ∧
    -Real.log (449889 / 500000) ≤ (105607213 / 1000000000) := by
  have h := checkLog_sound (w := (50111 / 949889)) (n := 12)
    (lo := (26401803 / 250000000)) (hi := (105607213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 449889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 449889) = 1/(449889 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6863 : Bounds (-105607213 / 1000000000) (-26401803 / 250000000) (Real.log (449889 / 500000)) := by
  have h := reflection_log_6863_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6864_neg : (47869589 / 500000000) ≤ -Real.log (125000 / 137559) ∧
    -Real.log (125000 / 137559) ≤ (95739179 / 1000000000) := by
  have h := checkLog_sound (w := (12559 / 262559)) (n := 12)
    (lo := (47869589 / 500000000)) (hi := (95739179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137559 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137559 / 125000) = 1/(125000 / 137559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6864 : Bounds (47869589 / 500000000) (95739179 / 1000000000) (Real.log (137559 / 125000)) := by
  have h := reflection_log_6864_neg
  have he : Real.log (137559 / 125000) = -Real.log (125000 / 137559) := by
    rw [show ((137559 / 125000) : ℝ) = ((125000 / 137559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6865_neg : (105885097 / 1000000000) ≤ -Real.log (112441 / 125000) ∧
    -Real.log (112441 / 125000) ≤ (52942549 / 500000000) := by
  have h := checkLog_sound (w := (12559 / 237441)) (n := 12)
    (lo := (105885097 / 1000000000)) (hi := (52942549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 112441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 112441) = 1/(112441 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6865 : Bounds (-52942549 / 500000000) (-105885097 / 1000000000) (Real.log (112441 / 125000)) := by
  have h := reflection_log_6865_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6866_neg : (5072959 / 500000000) ≤ -Real.log (15467271519 / 15625000000) ∧
    -Real.log (15467271519 / 15625000000) ≤ (10145919 / 1000000000) := by
  have h := checkLog_sound (w := (157728481 / 31092271519)) (n := 12)
    (lo := (5072959 / 500000000)) (hi := (10145919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15467271519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15467271519) = 1/(15467271519 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6866 : Bounds (-10145919 / 1000000000) (-5072959 / 500000000) (Real.log (15467271519 / 15625000000)) := by
  have h := reflection_log_6866_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6867_neg : (2019047 / 200000000) ≤ -Real.log (247488887679 / 250000000000) ∧
    -Real.log (247488887679 / 250000000000) ≤ (2523809 / 250000000) := by
  have h := checkLog_sound (w := (2511112321 / 497488887679)) (n := 12)
    (lo := (2019047 / 200000000)) (hi := (2523809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247488887679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247488887679) = 1/(247488887679 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6867 : Bounds (-2523809 / 250000000) (-2019047 / 200000000) (Real.log (247488887679 / 250000000000)) := by
  have h := reflection_log_6867_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6868_neg : (20111919 / 100000000) ≤ -Real.log (250000000000 / 305692626403) ∧
    -Real.log (250000000000 / 305692626403) ≤ (201119191 / 1000000000) := by
  have h := checkLog_sound (w := (55692626403 / 555692626403)) (n := 12)
    (lo := (20111919 / 100000000)) (hi := (201119191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305692626403 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305692626403 / 250000000000) = 1/(250000000000 / 305692626403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6868 : Bounds (20111919 / 100000000) (201119191 / 1000000000) (Real.log (305692626403 / 250000000000)) := by
  have h := reflection_log_6868_neg
  have he : Real.log (305692626403 / 250000000000) = -Real.log (250000000000 / 305692626403) := by
    rw [show ((305692626403 / 250000000000) : ℝ) = ((250000000000 / 305692626403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6869_neg : (50406069 / 250000000) ≤ -Real.log (125000000000 / 152923533231) ∧
    -Real.log (125000000000 / 152923533231) ≤ (201624277 / 1000000000) := by
  have h := checkLog_sound (w := (27923533231 / 277923533231)) (n := 12)
    (lo := (50406069 / 250000000)) (hi := (201624277 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152923533231 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152923533231 / 125000000000) = 1/(125000000000 / 152923533231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6869 : Bounds (50406069 / 250000000) (201624277 / 1000000000) (Real.log (152923533231 / 125000000000)) := by
  have h := reflection_log_6869_neg
  have he : Real.log (152923533231 / 125000000000) = -Real.log (125000000000 / 152923533231) := by
    rw [show ((152923533231 / 125000000000) : ℝ) = ((125000000000 / 152923533231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6870_neg : (201899359 / 500000000) ≤ -Real.log (500000000000 / 748751248751) ∧
    -Real.log (500000000000 / 748751248751) ≤ (403798719 / 1000000000) := by
  have h := checkLog_sound (w := (248751248751 / 1248751248751)) (n := 12)
    (lo := (201899359 / 500000000)) (hi := (403798719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((748751248751 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(748751248751 / 500000000000) = 1/(500000000000 / 748751248751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6870 : Bounds (201899359 / 500000000) (403798719 / 1000000000) (Real.log (748751248751 / 500000000000)) := by
  have h := reflection_log_6870_neg
  have he : Real.log (748751248751 / 500000000000) = -Real.log (500000000000 / 748751248751) := by
    rw [show ((748751248751 / 500000000000) : ℝ) = ((500000000000 / 748751248751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6871_neg : (404006987 / 1000000000) ≤ -Real.log (100000000000 / 149781441239) ∧
    -Real.log (100000000000 / 149781441239) ≤ (101001747 / 250000000) := by
  have h := checkLog_sound (w := (49781441239 / 249781441239)) (n := 12)
    (lo := (404006987 / 1000000000)) (hi := (101001747 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149781441239 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149781441239 / 100000000000) = 1/(100000000000 / 149781441239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6871 : Bounds (404006987 / 1000000000) (101001747 / 250000000) (Real.log (149781441239 / 100000000000)) := by
  have h := reflection_log_6871_neg
  have he : Real.log (149781441239 / 100000000000) = -Real.log (100000000000 / 149781441239) := by
    rw [show ((149781441239 / 100000000000) : ℝ) = ((100000000000 / 149781441239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6872_neg : (181821431 / 1000000000) ≤ -Real.log (5000 / 5997) ∧
    -Real.log (5000 / 5997) ≤ (22727679 / 125000000) := by
  have h := checkLog_sound (w := (997 / 10997)) (n := 12)
    (lo := (181821431 / 1000000000)) (hi := (22727679 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5997 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5997 / 5000) = 1/(5000 / 5997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6872 : Bounds (181821431 / 1000000000) (22727679 / 125000000) (Real.log (5997 / 5000)) := by
  have h := reflection_log_6872_neg
  have he : Real.log (5997 / 5000) = -Real.log (5000 / 5997) := by
    rw [show ((5997 / 5000) : ℝ) = ((5000 / 5997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6873_neg : (27799229 / 125000000) ≤ -Real.log (4003 / 5000) ∧
    -Real.log (4003 / 5000) ≤ (222393833 / 1000000000) := by
  have h := checkLog_sound (w := (997 / 9003)) (n := 12)
    (lo := (27799229 / 125000000)) (hi := (222393833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4003) = 1/(4003 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6873 : Bounds (-222393833 / 1000000000) (-27799229 / 125000000) (Real.log (4003 / 5000)) := by
  have h := reflection_log_6873_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6874_neg : (9969 / 50000000) ≤ -Real.log (5000000 / 5000997) ∧
    -Real.log (5000000 / 5000997) ≤ (199381 / 1000000000) := by
  have h := checkLog_sound (w := (997 / 10000997)) (n := 12)
    (lo := (9969 / 50000000)) (hi := (199381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000997 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000997 / 5000000) = 1/(5000000 / 5000997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6874 : Bounds (9969 / 50000000) (199381 / 1000000000) (Real.log (5000997 / 5000000)) := by
  have h := reflection_log_6874_neg
  have he : Real.log (5000997 / 5000000) = -Real.log (5000000 / 5000997) := by
    rw [show ((5000997 / 5000000) : ℝ) = ((5000000 / 5000997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6875_neg : (199419 / 1000000000) ≤ -Real.log (4999003 / 5000000) ∧
    -Real.log (4999003 / 5000000) ≤ (9971 / 50000000) := by
  have h := checkLog_sound (w := (997 / 9999003)) (n := 12)
    (lo := (199419 / 1000000000)) (hi := (9971 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999003) = 1/(4999003 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6875 : Bounds (-9971 / 50000000) (-199419 / 1000000000) (Real.log (4999003 / 5000000)) := by
  have h := reflection_log_6875_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6876_neg : (9555833 / 100000000) ≤ -Real.log (1000000 / 1100273) ∧
    -Real.log (1000000 / 1100273) ≤ (95558331 / 1000000000) := by
  have h := checkLog_sound (w := (100273 / 2100273)) (n := 12)
    (lo := (9555833 / 100000000)) (hi := (95558331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1100273 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1100273 / 1000000) = 1/(1000000 / 1100273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6876 : Bounds (9555833 / 100000000) (95558331 / 1000000000) (Real.log (1100273 / 1000000)) := by
  have h := reflection_log_6876_neg
  have he : Real.log (1100273 / 1000000) = -Real.log (1000000 / 1100273) := by
    rw [show ((1100273 / 1000000) : ℝ) = ((1000000 / 1100273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6877_neg : (21132779 / 200000000) ≤ -Real.log (899727 / 1000000) ∧
    -Real.log (899727 / 1000000) ≤ (13207987 / 125000000) := by
  have h := checkLog_sound (w := (100273 / 1899727)) (n := 12)
    (lo := (21132779 / 200000000)) (hi := (13207987 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 899727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 899727) = 1/(899727 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6877 : Bounds (-13207987 / 125000000) (-21132779 / 200000000) (Real.log (899727 / 1000000)) := by
  have h := reflection_log_6877_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6878_neg : (95785521 / 1000000000) ≤ -Real.log (1000000 / 1100523) ∧
    -Real.log (1000000 / 1100523) ≤ (47892761 / 500000000) := by
  have h := checkLog_sound (w := (100523 / 2100523)) (n := 12)
    (lo := (95785521 / 1000000000)) (hi := (47892761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1100523 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1100523 / 1000000) = 1/(1000000 / 1100523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6878 : Bounds (95785521 / 1000000000) (47892761 / 500000000) (Real.log (1100523 / 1000000)) := by
  have h := reflection_log_6878_neg
  have he : Real.log (1100523 / 1000000) = -Real.log (1000000 / 1100523) := by
    rw [show ((1100523 / 1000000) : ℝ) = ((1000000 / 1100523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6879_neg : (21188359 / 200000000) ≤ -Real.log (899477 / 1000000) ∧
    -Real.log (899477 / 1000000) ≤ (26485449 / 250000000) := by
  have h := checkLog_sound (w := (100523 / 1899477)) (n := 12)
    (lo := (21188359 / 200000000)) (hi := (26485449 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 899477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 899477) = 1/(899477 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6879 : Bounds (-26485449 / 250000000) (-21188359 / 200000000) (Real.log (899477 / 1000000)) := by
  have h := reflection_log_6879_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6880_neg : (5078137 / 500000000) ≤ -Real.log (989895126471 / 1000000000000) ∧
    -Real.log (989895126471 / 1000000000000) ≤ (406251 / 40000000) := by
  have h := checkLog_sound (w := (10104873529 / 1989895126471)) (n := 12)
    (lo := (5078137 / 500000000)) (hi := (406251 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989895126471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989895126471) = 1/(989895126471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6880 : Bounds (-406251 / 40000000) (-5078137 / 500000000) (Real.log (989895126471 / 1000000000000)) := by
  have h := reflection_log_6880_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6881_neg : (2526391 / 250000000) ≤ -Real.log (989945325471 / 1000000000000) ∧
    -Real.log (989945325471 / 1000000000000) ≤ (2021113 / 200000000) := by
  have h := checkLog_sound (w := (10054674529 / 1989945325471)) (n := 12)
    (lo := (2526391 / 250000000)) (hi := (2021113 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989945325471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989945325471) = 1/(989945325471 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6881 : Bounds (-2021113 / 200000000) (-2526391 / 250000000) (Real.log (989945325471 / 1000000000000)) := by
  have h := reflection_log_6881_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6882_neg : (8048889 / 40000000) ≤ -Real.log (500000000000 / 611448250413) ∧
    -Real.log (500000000000 / 611448250413) ≤ (100611113 / 500000000) := by
  have h := checkLog_sound (w := (111448250413 / 1111448250413)) (n := 12)
    (lo := (8048889 / 40000000)) (hi := (100611113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611448250413 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611448250413 / 500000000000) = 1/(500000000000 / 611448250413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6882 : Bounds (8048889 / 40000000) (100611113 / 500000000) (Real.log (611448250413 / 500000000000)) := by
  have h := reflection_log_6882_neg
  have he : Real.log (611448250413 / 500000000000) = -Real.log (500000000000 / 611448250413) := by
    rw [show ((611448250413 / 500000000000) : ℝ) = ((500000000000 / 611448250413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6883_neg : (201727317 / 1000000000) ≤ -Real.log (500000000000 / 611757165553) ∧
    -Real.log (500000000000 / 611757165553) ≤ (100863659 / 500000000) := by
  have h := checkLog_sound (w := (111757165553 / 1111757165553)) (n := 12)
    (lo := (201727317 / 1000000000)) (hi := (100863659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611757165553 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611757165553 / 500000000000) = 1/(500000000000 / 611757165553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6883 : Bounds (201727317 / 1000000000) (100863659 / 500000000) (Real.log (611757165553 / 500000000000)) := by
  have h := reflection_log_6883_neg
  have he : Real.log (611757165553 / 500000000000) = -Real.log (500000000000 / 611757165553) := by
    rw [show ((611757165553 / 500000000000) : ℝ) = ((500000000000 / 611757165553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6884_neg : (404006987 / 1000000000) ≤ -Real.log (250000000000 / 374453603097) ∧
    -Real.log (250000000000 / 374453603097) ≤ (101001747 / 250000000) := by
  have h := checkLog_sound (w := (124453603097 / 624453603097)) (n := 12)
    (lo := (404006987 / 1000000000)) (hi := (101001747 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374453603097 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374453603097 / 250000000000) = 1/(250000000000 / 374453603097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6884 : Bounds (404006987 / 1000000000) (101001747 / 250000000) (Real.log (374453603097 / 250000000000)) := by
  have h := reflection_log_6884_neg
  have he : Real.log (374453603097 / 250000000000) = -Real.log (250000000000 / 374453603097) := by
    rw [show ((374453603097 / 250000000000) : ℝ) = ((250000000000 / 374453603097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6885_neg : (12631727 / 31250000) ≤ -Real.log (500000000000 / 749063202599) ∧
    -Real.log (500000000000 / 749063202599) ≤ (80843053 / 200000000) := by
  have h := checkLog_sound (w := (249063202599 / 1249063202599)) (n := 12)
    (lo := (12631727 / 31250000)) (hi := (80843053 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((749063202599 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(749063202599 / 500000000000) = 1/(500000000000 / 749063202599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6885 : Bounds (12631727 / 31250000) (80843053 / 200000000) (Real.log (749063202599 / 500000000000)) := by
  have h := reflection_log_6885_neg
  have he : Real.log (749063202599 / 500000000000) = -Real.log (500000000000 / 749063202599) := by
    rw [show ((749063202599 / 500000000000) : ℝ) = ((500000000000 / 749063202599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6886_neg : (181904803 / 1000000000) ≤ -Real.log (2000 / 2399) ∧
    -Real.log (2000 / 2399) ≤ (45476201 / 250000000) := by
  have h := checkLog_sound (w := (399 / 4399)) (n := 12)
    (lo := (181904803 / 1000000000)) (hi := (45476201 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2399 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2399 / 2000) = 1/(2000 / 2399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6886 : Bounds (181904803 / 1000000000) (45476201 / 250000000) (Real.log (2399 / 2000)) := by
  have h := reflection_log_6886_neg
  have he : Real.log (2399 / 2000) = -Real.log (2000 / 2399) := by
    rw [show ((2399 / 2000) : ℝ) = ((2000 / 2399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6887_neg : (111259373 / 500000000) ≤ -Real.log (1601 / 2000) ∧
    -Real.log (1601 / 2000) ≤ (222518747 / 1000000000) := by
  have h := checkLog_sound (w := (399 / 3601)) (n := 12)
    (lo := (111259373 / 500000000)) (hi := (222518747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1601) = 1/(1601 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6887 : Bounds (-222518747 / 1000000000) (-111259373 / 500000000) (Real.log (1601 / 2000)) := by
  have h := reflection_log_6887_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6888_neg : (4987 / 25000000) ≤ -Real.log (2000000 / 2000399) ∧
    -Real.log (2000000 / 2000399) ≤ (199481 / 1000000000) := by
  have h := checkLog_sound (w := (399 / 4000399)) (n := 12)
    (lo := (4987 / 25000000)) (hi := (199481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000399 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000399 / 2000000) = 1/(2000000 / 2000399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6888 : Bounds (4987 / 25000000) (199481 / 1000000000) (Real.log (2000399 / 2000000)) := by
  have h := reflection_log_6888_neg
  have he : Real.log (2000399 / 2000000) = -Real.log (2000000 / 2000399) := by
    rw [show ((2000399 / 2000000) : ℝ) = ((2000000 / 2000399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6889_neg : (199519 / 1000000000) ≤ -Real.log (1999601 / 2000000) ∧
    -Real.log (1999601 / 2000000) ≤ (1247 / 6250000) := by
  have h := checkLog_sound (w := (399 / 3999601)) (n := 12)
    (lo := (199519 / 1000000000)) (hi := (1247 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999601) = 1/(1999601 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6889 : Bounds (-1247 / 6250000) (-199519 / 1000000000) (Real.log (1999601 / 2000000)) := by
  have h := reflection_log_6889_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6890_neg : (95604681 / 1000000000) ≤ -Real.log (250000 / 275081) ∧
    -Real.log (250000 / 275081) ≤ (47802341 / 500000000) := by
  have h := checkLog_sound (w := (25081 / 525081)) (n := 12)
    (lo := (95604681 / 1000000000)) (hi := (47802341 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((275081 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(275081 / 250000) = 1/(250000 / 275081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6890 : Bounds (95604681 / 1000000000) (47802341 / 500000000) (Real.log (275081 / 250000)) := by
  have h := reflection_log_6890_neg
  have he : Real.log (275081 / 250000) = -Real.log (250000 / 275081) := by
    rw [show ((275081 / 250000) : ℝ) = ((250000 / 275081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6891_neg : (5286029 / 50000000) ≤ -Real.log (224919 / 250000) ∧
    -Real.log (224919 / 250000) ≤ (105720581 / 1000000000) := by
  have h := checkLog_sound (w := (25081 / 474919)) (n := 12)
    (lo := (5286029 / 50000000)) (hi := (105720581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 224919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 224919) = 1/(224919 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6891 : Bounds (-105720581 / 1000000000) (-5286029 / 50000000) (Real.log (224919 / 250000)) := by
  have h := reflection_log_6891_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6892_neg : (95831861 / 1000000000) ≤ -Real.log (500000 / 550287) ∧
    -Real.log (500000 / 550287) ≤ (47915931 / 500000000) := by
  have h := checkLog_sound (w := (50287 / 1050287)) (n := 12)
    (lo := (95831861 / 1000000000)) (hi := (47915931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((550287 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(550287 / 500000) = 1/(500000 / 550287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6892 : Bounds (95831861 / 1000000000) (47915931 / 500000000) (Real.log (550287 / 500000)) := by
  have h := reflection_log_6892_neg
  have he : Real.log (550287 / 500000) = -Real.log (500000 / 550287) := by
    rw [show ((550287 / 500000) : ℝ) = ((500000 / 550287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6893_neg : (3312453 / 31250000) ≤ -Real.log (449713 / 500000) ∧
    -Real.log (449713 / 500000) ≤ (105998497 / 1000000000) := by
  have h := checkLog_sound (w := (50287 / 949713)) (n := 12)
    (lo := (3312453 / 31250000)) (hi := (105998497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 449713) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 449713) = 1/(449713 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6893 : Bounds (-105998497 / 1000000000) (-3312453 / 31250000) (Real.log (449713 / 500000)) := by
  have h := reflection_log_6893_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6894_neg : (2033327 / 200000000) ≤ -Real.log (247471217631 / 250000000000) ∧
    -Real.log (247471217631 / 250000000000) ≤ (2541659 / 250000000) := by
  have h := checkLog_sound (w := (2528782369 / 497471217631)) (n := 12)
    (lo := (2033327 / 200000000)) (hi := (2541659 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247471217631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247471217631) = 1/(247471217631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6894 : Bounds (-2541659 / 250000000) (-2033327 / 200000000) (Real.log (247471217631 / 250000000000)) := by
  have h := reflection_log_6894_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6895_neg : (5057949 / 500000000) ≤ -Real.log (61870943439 / 62500000000) ∧
    -Real.log (61870943439 / 62500000000) ≤ (10115899 / 1000000000) := by
  have h := checkLog_sound (w := (629056561 / 124370943439)) (n := 12)
    (lo := (5057949 / 500000000)) (hi := (10115899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61870943439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61870943439) = 1/(61870943439 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6895 : Bounds (-10115899 / 1000000000) (-5057949 / 500000000) (Real.log (61870943439 / 62500000000)) := by
  have h := reflection_log_6895_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6896_neg : (100662631 / 500000000) ≤ -Real.log (250000000000 / 305755627581) ∧
    -Real.log (250000000000 / 305755627581) ≤ (201325263 / 1000000000) := by
  have h := checkLog_sound (w := (55755627581 / 555755627581)) (n := 12)
    (lo := (100662631 / 500000000)) (hi := (201325263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((305755627581 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(305755627581 / 250000000000) = 1/(250000000000 / 305755627581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6896 : Bounds (100662631 / 500000000) (201325263 / 1000000000) (Real.log (305755627581 / 250000000000)) := by
  have h := reflection_log_6896_neg
  have he : Real.log (305755627581 / 250000000000) = -Real.log (250000000000 / 305755627581) := by
    rw [show ((305755627581 / 250000000000) : ℝ) = ((250000000000 / 305755627581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6897_neg : (100915179 / 500000000) ≤ -Real.log (500000000000 / 611820205331) ∧
    -Real.log (500000000000 / 611820205331) ≤ (201830359 / 1000000000) := by
  have h := checkLog_sound (w := (111820205331 / 1111820205331)) (n := 12)
    (lo := (100915179 / 500000000)) (hi := (201830359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611820205331 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611820205331 / 500000000000) = 1/(500000000000 / 611820205331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6897 : Bounds (100915179 / 500000000) (201830359 / 1000000000) (Real.log (611820205331 / 500000000000)) := by
  have h := reflection_log_6897_neg
  have he : Real.log (611820205331 / 500000000000) = -Real.log (500000000000 / 611820205331) := by
    rw [show ((611820205331 / 500000000000) : ℝ) = ((500000000000 / 611820205331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6898_neg : (12631727 / 31250000) ≤ -Real.log (250000000000 / 374531601299) ∧
    -Real.log (250000000000 / 374531601299) ≤ (80843053 / 200000000) := by
  have h := checkLog_sound (w := (124531601299 / 624531601299)) (n := 12)
    (lo := (12631727 / 31250000)) (hi := (80843053 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374531601299 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374531601299 / 250000000000) = 1/(250000000000 / 374531601299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6898 : Bounds (12631727 / 31250000) (80843053 / 200000000) (Real.log (374531601299 / 250000000000)) := by
  have h := reflection_log_6898_neg
  have he : Real.log (374531601299 / 250000000000) = -Real.log (250000000000 / 374531601299) := by
    rw [show ((374531601299 / 250000000000) : ℝ) = ((250000000000 / 374531601299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6899_neg : (404423549 / 1000000000) ≤ -Real.log (500000000000 / 749219237977) ∧
    -Real.log (500000000000 / 749219237977) ≤ (8088471 / 20000000) := by
  have h := checkLog_sound (w := (249219237977 / 1249219237977)) (n := 12)
    (lo := (404423549 / 1000000000)) (hi := (8088471 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((749219237977 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(749219237977 / 500000000000) = 1/(500000000000 / 749219237977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6899 : Bounds (404423549 / 1000000000) (8088471 / 20000000) (Real.log (749219237977 / 500000000000)) := by
  have h := reflection_log_6899_neg
  have he : Real.log (749219237977 / 500000000000) = -Real.log (500000000000 / 749219237977) := by
    rw [show ((749219237977 / 500000000000) : ℝ) = ((500000000000 / 749219237977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6900_neg : (181988167 / 1000000000) ≤ -Real.log (2500 / 2999) ∧
    -Real.log (2500 / 2999) ≤ (22748521 / 125000000) := by
  have h := checkLog_sound (w := (499 / 5499)) (n := 12)
    (lo := (181988167 / 1000000000)) (hi := (22748521 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2999 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2999 / 2500) = 1/(2500 / 2999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6900 : Bounds (181988167 / 1000000000) (22748521 / 125000000) (Real.log (2999 / 2500)) := by
  have h := reflection_log_6900_neg
  have he : Real.log (2999 / 2500) = -Real.log (2500 / 2999) := by
    rw [show ((2999 / 2500) : ℝ) = ((2500 / 2999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6901_neg : (55660919 / 250000000) ≤ -Real.log (2001 / 2500) ∧
    -Real.log (2001 / 2500) ≤ (222643677 / 1000000000) := by
  have h := checkLog_sound (w := (499 / 4501)) (n := 12)
    (lo := (55660919 / 250000000)) (hi := (222643677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2001) = 1/(2001 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6901 : Bounds (-222643677 / 1000000000) (-55660919 / 250000000) (Real.log (2001 / 2500)) := by
  have h := reflection_log_6901_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6902_neg : (9979 / 50000000) ≤ -Real.log (2500000 / 2500499) ∧
    -Real.log (2500000 / 2500499) ≤ (199581 / 1000000000) := by
  have h := checkLog_sound (w := (499 / 5000499)) (n := 12)
    (lo := (9979 / 50000000)) (hi := (199581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500499 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500499 / 2500000) = 1/(2500000 / 2500499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6902 : Bounds (9979 / 50000000) (199581 / 1000000000) (Real.log (2500499 / 2500000)) := by
  have h := reflection_log_6902_neg
  have he : Real.log (2500499 / 2500000) = -Real.log (2500000 / 2500499) := by
    rw [show ((2500499 / 2500000) : ℝ) = ((2500000 / 2500499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6903_neg : (199619 / 1000000000) ≤ -Real.log (2499501 / 2500000) ∧
    -Real.log (2499501 / 2500000) ≤ (9981 / 50000000) := by
  have h := checkLog_sound (w := (499 / 4999501)) (n := 12)
    (lo := (199619 / 1000000000)) (hi := (9981 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499501) = 1/(2499501 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6903 : Bounds (-9981 / 50000000) (-199619 / 1000000000) (Real.log (2499501 / 2500000)) := by
  have h := reflection_log_6903_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6904_neg : (9565103 / 100000000) ≤ -Real.log (8000 / 8803) ∧
    -Real.log (8000 / 8803) ≤ (95651031 / 1000000000) := by
  have h := checkLog_sound (w := (803 / 16803)) (n := 12)
    (lo := (9565103 / 100000000)) (hi := (95651031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8803 / 8000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8803 / 8000) = 1/(8000 / 8803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6904 : Bounds (9565103 / 100000000) (95651031 / 1000000000) (Real.log (8803 / 8000)) := by
  have h := reflection_log_6904_neg
  have he : Real.log (8803 / 8000) = -Real.log (8000 / 8803) := by
    rw [show ((8803 / 8000) : ℝ) = ((8000 / 8803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6905_neg : (105777269 / 1000000000) ≤ -Real.log (7197 / 8000) ∧
    -Real.log (7197 / 8000) ≤ (10577727 / 100000000) := by
  have h := checkLog_sound (w := (803 / 15197)) (n := 12)
    (lo := (105777269 / 1000000000)) (hi := (10577727 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8000 / 7197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8000 / 7197) = 1/(7197 / 8000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6905 : Bounds (-10577727 / 100000000) (-105777269 / 1000000000) (Real.log (7197 / 8000)) := by
  have h := reflection_log_6905_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6906_neg : (479391 / 5000000) ≤ -Real.log (1600 / 1761) ∧
    -Real.log (1600 / 1761) ≤ (95878201 / 1000000000) := by
  have h := checkLog_sound (w := (161 / 3361)) (n := 12)
    (lo := (479391 / 5000000)) (hi := (95878201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1761 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1761 / 1600) = 1/(1600 / 1761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6906 : Bounds (479391 / 5000000) (95878201 / 1000000000) (Real.log (1761 / 1600)) := by
  have h := reflection_log_6906_neg
  have he : Real.log (1761 / 1600) = -Real.log (1600 / 1761) := by
    rw [show ((1761 / 1600) : ℝ) = ((1600 / 1761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6907_neg : (106055201 / 1000000000) ≤ -Real.log (1439 / 1600) ∧
    -Real.log (1439 / 1600) ≤ (53027601 / 500000000) := by
  have h := checkLog_sound (w := (161 / 3039)) (n := 12)
    (lo := (106055201 / 1000000000)) (hi := (53027601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600 / 1439) = 1/(1439 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6907 : Bounds (-53027601 / 500000000) (-106055201 / 1000000000) (Real.log (1439 / 1600)) := by
  have h := reflection_log_6907_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6908_neg : (10177001 / 1000000000) ≤ -Real.log (2534079 / 2560000) ∧
    -Real.log (2534079 / 2560000) ≤ (5088501 / 500000000) := by
  have h := checkLog_sound (w := (25921 / 5094079)) (n := 12)
    (lo := (10177001 / 1000000000)) (hi := (5088501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560000 / 2534079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560000 / 2534079) = 1/(2534079 / 2560000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6908 : Bounds (-5088501 / 500000000) (-10177001 / 1000000000) (Real.log (2534079 / 2560000)) := by
  have h := reflection_log_6908_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6909_neg : (5063119 / 500000000) ≤ -Real.log (63355191 / 64000000) ∧
    -Real.log (63355191 / 64000000) ≤ (10126239 / 1000000000) := by
  have h := checkLog_sound (w := (644809 / 127355191)) (n := 12)
    (lo := (5063119 / 500000000)) (hi := (10126239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64000000 / 63355191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(64000000 / 63355191) = 1/(63355191 / 64000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6909 : Bounds (-10126239 / 1000000000) (-5063119 / 500000000) (Real.log (63355191 / 64000000)) := by
  have h := reflection_log_6909_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_6910_neg : (201428299 / 1000000000) ≤ -Real.log (100000000000 / 122314853411) ∧
    -Real.log (100000000000 / 122314853411) ≤ (2014283 / 10000000) := by
  have h := checkLog_sound (w := (22314853411 / 222314853411)) (n := 12)
    (lo := (201428299 / 1000000000)) (hi := (2014283 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122314853411 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122314853411 / 100000000000) = 1/(100000000000 / 122314853411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6910 : Bounds (201428299 / 1000000000) (2014283 / 10000000) (Real.log (122314853411 / 100000000000)) := by
  have h := reflection_log_6910_neg
  have he : Real.log (122314853411 / 100000000000) = -Real.log (100000000000 / 122314853411) := by
    rw [show ((122314853411 / 100000000000) : ℝ) = ((100000000000 / 122314853411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6911_neg : (201933401 / 1000000000) ≤ -Real.log (500000000000 / 611883252259) ∧
    -Real.log (500000000000 / 611883252259) ≤ (100966701 / 500000000) := by
  have h := checkLog_sound (w := (111883252259 / 1111883252259)) (n := 12)
    (lo := (201933401 / 1000000000)) (hi := (100966701 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611883252259 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611883252259 / 500000000000) = 1/(500000000000 / 611883252259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6911 : Bounds (201933401 / 1000000000) (100966701 / 500000000) (Real.log (611883252259 / 500000000000)) := by
  have h := reflection_log_6911_neg
  have he : Real.log (611883252259 / 500000000000) = -Real.log (500000000000 / 611883252259) := by
    rw [show ((611883252259 / 500000000000) : ℝ) = ((500000000000 / 611883252259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
