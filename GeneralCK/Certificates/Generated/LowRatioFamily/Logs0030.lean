import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1920_neg : (164013 / 1000000000) ≤ -Real.log (249959 / 250000) ∧
    -Real.log (249959 / 250000) ≤ (82007 / 500000000) := by
  have h := checkLog_sound (w := (41 / 499959)) (n := 12)
    (lo := (164013 / 1000000000)) (hi := (82007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249959) = 1/(249959 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1920 : Bounds (-82007 / 500000000) (-164013 / 1000000000) (Real.log (249959 / 250000)) := by
  have h := reflection_log_1920_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1921_neg : (79058839 / 1000000000) ≤ -Real.log (250000 / 270567) ∧
    -Real.log (250000 / 270567) ≤ (1976471 / 25000000) := by
  have h := checkLog_sound (w := (20567 / 520567)) (n := 12)
    (lo := (79058839 / 1000000000)) (hi := (1976471 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270567 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270567 / 250000) = 1/(250000 / 270567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1921 : Bounds (79058839 / 1000000000) (1976471 / 25000000) (Real.log (270567 / 250000)) := by
  have h := reflection_log_1921_neg
  have he : Real.log (270567 / 250000) = -Real.log (250000 / 270567) := by
    rw [show ((270567 / 250000) : ℝ) = ((250000 / 270567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1922_neg : (85849869 / 1000000000) ≤ -Real.log (229433 / 250000) ∧
    -Real.log (229433 / 250000) ≤ (8584987 / 100000000) := by
  have h := checkLog_sound (w := (20567 / 479433)) (n := 12)
    (lo := (85849869 / 1000000000)) (hi := (8584987 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229433) = 1/(229433 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1922 : Bounds (-8584987 / 100000000) (-85849869 / 1000000000) (Real.log (229433 / 250000)) := by
  have h := reflection_log_1922_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1923_neg : (19814369 / 250000000) ≤ -Real.log (1000000 / 1082483) ∧
    -Real.log (1000000 / 1082483) ≤ (79257477 / 1000000000) := by
  have h := checkLog_sound (w := (82483 / 2082483)) (n := 12)
    (lo := (19814369 / 250000000)) (hi := (79257477 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082483 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082483 / 1000000) = 1/(1000000 / 1082483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1923 : Bounds (19814369 / 250000000) (79257477 / 1000000000) (Real.log (1082483 / 1000000)) := by
  have h := reflection_log_1923_neg
  have he : Real.log (1082483 / 1000000) = -Real.log (1000000 / 1082483) := by
    rw [show ((1082483 / 1000000) : ℝ) = ((1000000 / 1082483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1924_neg : (8608417 / 100000000) ≤ -Real.log (917517 / 1000000) ∧
    -Real.log (917517 / 1000000) ≤ (86084171 / 1000000000) := by
  have h := checkLog_sound (w := (82483 / 1917517)) (n := 12)
    (lo := (8608417 / 100000000)) (hi := (86084171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917517) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917517) = 1/(917517 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1924 : Bounds (-86084171 / 1000000000) (-8608417 / 100000000) (Real.log (917517 / 1000000)) := by
  have h := reflection_log_1924_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1925_neg : (3413347 / 500000000) ≤ -Real.log (993196554711 / 1000000000000) ∧
    -Real.log (993196554711 / 1000000000000) ≤ (1365339 / 200000000) := by
  have h := checkLog_sound (w := (6803445289 / 1993196554711)) (n := 12)
    (lo := (3413347 / 500000000)) (hi := (1365339 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993196554711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993196554711) = 1/(993196554711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1925 : Bounds (-1365339 / 200000000) (-3413347 / 500000000) (Real.log (993196554711 / 1000000000000)) := by
  have h := reflection_log_1925_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1926_neg : (679103 / 100000000) ≤ -Real.log (62076998511 / 62500000000) ∧
    -Real.log (62076998511 / 62500000000) ≤ (6791031 / 1000000000) := by
  have h := checkLog_sound (w := (423001489 / 124576998511)) (n := 12)
    (lo := (679103 / 100000000)) (hi := (6791031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62076998511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62076998511) = 1/(62076998511 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1926 : Bounds (-6791031 / 1000000000) (-679103 / 100000000) (Real.log (62076998511 / 62500000000)) := by
  have h := reflection_log_1926_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1927_neg : (164908709 / 1000000000) ≤ -Real.log (250000000000 / 294821363971) ∧
    -Real.log (250000000000 / 294821363971) ≤ (16490871 / 100000000) := by
  have h := checkLog_sound (w := (44821363971 / 544821363971)) (n := 12)
    (lo := (164908709 / 1000000000)) (hi := (16490871 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294821363971 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294821363971 / 250000000000) = 1/(250000000000 / 294821363971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1927 : Bounds (164908709 / 1000000000) (16490871 / 100000000) (Real.log (294821363971 / 250000000000)) := by
  have h := reflection_log_1927_neg
  have he : Real.log (294821363971 / 250000000000) = -Real.log (250000000000 / 294821363971) := by
    rw [show ((294821363971 / 250000000000) : ℝ) = ((250000000000 / 294821363971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1928_neg : (82670823 / 500000000) ≤ -Real.log (100000000000 / 117979612367) ∧
    -Real.log (100000000000 / 117979612367) ≤ (165341647 / 1000000000) := by
  have h := checkLog_sound (w := (17979612367 / 217979612367)) (n := 12)
    (lo := (82670823 / 500000000)) (hi := (165341647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117979612367 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117979612367 / 100000000000) = 1/(100000000000 / 117979612367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1928 : Bounds (82670823 / 500000000) (165341647 / 1000000000) (Real.log (117979612367 / 100000000000)) := by
  have h := reflection_log_1928_neg
  have he : Real.log (117979612367 / 100000000000) = -Real.log (100000000000 / 117979612367) := by
    rw [show ((117979612367 / 100000000000) : ℝ) = ((100000000000 / 117979612367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1929_neg : (33078349 / 100000000) ≤ -Real.log (62500000000 / 87003647889) ∧
    -Real.log (62500000000 / 87003647889) ≤ (330783491 / 1000000000) := by
  have h := checkLog_sound (w := (24503647889 / 149503647889)) (n := 12)
    (lo := (33078349 / 100000000)) (hi := (330783491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87003647889 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87003647889 / 62500000000) = 1/(62500000000 / 87003647889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1929 : Bounds (33078349 / 100000000) (330783491 / 1000000000) (Real.log (87003647889 / 62500000000)) := by
  have h := reflection_log_1929_neg
  have he : Real.log (87003647889 / 62500000000) = -Real.log (62500000000 / 87003647889) := by
    rw [show ((87003647889 / 62500000000) : ℝ) = ((62500000000 / 87003647889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1930_neg : (66197803 / 200000000) ≤ -Real.log (125000000000 / 174043062201) ∧
    -Real.log (125000000000 / 174043062201) ≤ (41373627 / 125000000) := by
  have h := checkLog_sound (w := (49043062201 / 299043062201)) (n := 12)
    (lo := (66197803 / 200000000)) (hi := (41373627 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((174043062201 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(174043062201 / 125000000000) = 1/(125000000000 / 174043062201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1930 : Bounds (66197803 / 200000000) (41373627 / 125000000) (Real.log (174043062201 / 125000000000)) := by
  have h := reflection_log_1930_neg
  have he : Real.log (174043062201 / 125000000000) = -Real.log (125000000000 / 174043062201) := by
    rw [show ((174043062201 / 125000000000) : ℝ) = ((125000000000 / 174043062201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1931_neg : (4748383 / 31250000) ≤ -Real.log (10000 / 11641) ∧
    -Real.log (10000 / 11641) ≤ (151948257 / 1000000000) := by
  have h := checkLog_sound (w := (1641 / 21641)) (n := 12)
    (lo := (4748383 / 31250000)) (hi := (151948257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11641 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11641 / 10000) = 1/(10000 / 11641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1931 : Bounds (4748383 / 31250000) (151948257 / 1000000000) (Real.log (11641 / 10000)) := by
  have h := reflection_log_1931_neg
  have he : Real.log (11641 / 10000) = -Real.log (10000 / 11641) := by
    rw [show ((11641 / 10000) : ℝ) = ((10000 / 11641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1932_neg : (17924629 / 100000000) ≤ -Real.log (8359 / 10000) ∧
    -Real.log (8359 / 10000) ≤ (179246291 / 1000000000) := by
  have h := checkLog_sound (w := (1641 / 18359)) (n := 12)
    (lo := (17924629 / 100000000)) (hi := (179246291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8359) = 1/(8359 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1932 : Bounds (-179246291 / 1000000000) (-17924629 / 100000000) (Real.log (8359 / 10000)) := by
  have h := reflection_log_1932_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1933_neg : (82043 / 500000000) ≤ -Real.log (10000000 / 10001641) ∧
    -Real.log (10000000 / 10001641) ≤ (164087 / 1000000000) := by
  have h := checkLog_sound (w := (1641 / 20001641)) (n := 12)
    (lo := (82043 / 500000000)) (hi := (164087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001641 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001641 / 10000000) = 1/(10000000 / 10001641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1933 : Bounds (82043 / 500000000) (164087 / 1000000000) (Real.log (10001641 / 10000000)) := by
  have h := reflection_log_1933_neg
  have he : Real.log (10001641 / 10000000) = -Real.log (10000000 / 10001641) := by
    rw [show ((10001641 / 10000000) : ℝ) = ((10000000 / 10001641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1934_neg : (164113 / 1000000000) ≤ -Real.log (9998359 / 10000000) ∧
    -Real.log (9998359 / 10000000) ≤ (82057 / 500000000) := by
  have h := checkLog_sound (w := (1641 / 19998359)) (n := 12)
    (lo := (164113 / 1000000000)) (hi := (82057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998359) = 1/(9998359 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1934 : Bounds (-82057 / 500000000) (-164113 / 1000000000) (Real.log (9998359 / 10000000)) := by
  have h := reflection_log_1934_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1935_neg : (79105961 / 1000000000) ≤ -Real.log (1000000 / 1082319) ∧
    -Real.log (1000000 / 1082319) ≤ (39552981 / 500000000) := by
  have h := checkLog_sound (w := (82319 / 2082319)) (n := 12)
    (lo := (79105961 / 1000000000)) (hi := (39552981 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082319 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082319 / 1000000) = 1/(1000000 / 1082319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1935 : Bounds (79105961 / 1000000000) (39552981 / 500000000) (Real.log (1082319 / 1000000)) := by
  have h := reflection_log_1935_neg
  have he : Real.log (1082319 / 1000000) = -Real.log (1000000 / 1082319) := by
    rw [show ((1082319 / 1000000) : ℝ) = ((1000000 / 1082319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1936_neg : (85905443 / 1000000000) ≤ -Real.log (917681 / 1000000) ∧
    -Real.log (917681 / 1000000) ≤ (21476361 / 250000000) := by
  have h := checkLog_sound (w := (82319 / 1917681)) (n := 12)
    (lo := (85905443 / 1000000000)) (hi := (21476361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917681) = 1/(917681 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1936 : Bounds (-21476361 / 250000000) (-85905443 / 1000000000) (Real.log (917681 / 1000000)) := by
  have h := reflection_log_1936_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1937_neg : (79304589 / 1000000000) ≤ -Real.log (500000 / 541267) ∧
    -Real.log (500000 / 541267) ≤ (7930459 / 100000000) := by
  have h := checkLog_sound (w := (41267 / 1041267)) (n := 12)
    (lo := (79304589 / 1000000000)) (hi := (7930459 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541267 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541267 / 500000) = 1/(500000 / 541267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1937 : Bounds (79304589 / 1000000000) (7930459 / 100000000) (Real.log (541267 / 500000)) := by
  have h := reflection_log_1937_neg
  have he : Real.log (541267 / 500000) = -Real.log (500000 / 541267) := by
    rw [show ((541267 / 500000) : ℝ) = ((500000 / 541267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1938_neg : (21534939 / 250000000) ≤ -Real.log (458733 / 500000) ∧
    -Real.log (458733 / 500000) ≤ (86139757 / 1000000000) := by
  have h := checkLog_sound (w := (41267 / 958733)) (n := 12)
    (lo := (21534939 / 250000000)) (hi := (86139757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458733) = 1/(458733 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1938 : Bounds (-86139757 / 1000000000) (-21534939 / 250000000) (Real.log (458733 / 500000)) := by
  have h := reflection_log_1938_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1939_neg : (6835167 / 1000000000) ≤ -Real.log (248297034711 / 250000000000) ∧
    -Real.log (248297034711 / 250000000000) ≤ (213599 / 31250000) := by
  have h := checkLog_sound (w := (1702965289 / 498297034711)) (n := 12)
    (lo := (6835167 / 1000000000)) (hi := (213599 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248297034711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248297034711) = 1/(248297034711 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1939 : Bounds (-213599 / 31250000) (-6835167 / 1000000000) (Real.log (248297034711 / 250000000000)) := by
  have h := reflection_log_1939_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1940_neg : (6799481 / 1000000000) ≤ -Real.log (993223582239 / 1000000000000) ∧
    -Real.log (993223582239 / 1000000000000) ≤ (3399741 / 500000000) := by
  have h := checkLog_sound (w := (6776417761 / 1993223582239)) (n := 12)
    (lo := (6799481 / 1000000000)) (hi := (3399741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993223582239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993223582239) = 1/(993223582239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1940 : Bounds (-3399741 / 500000000) (-6799481 / 1000000000) (Real.log (993223582239 / 1000000000000)) := by
  have h := reflection_log_1940_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1941_neg : (41252851 / 250000000) ≤ -Real.log (125000000000 / 147425821173) ∧
    -Real.log (125000000000 / 147425821173) ≤ (33002281 / 200000000) := by
  have h := checkLog_sound (w := (22425821173 / 272425821173)) (n := 12)
    (lo := (41252851 / 250000000)) (hi := (33002281 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147425821173 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147425821173 / 125000000000) = 1/(125000000000 / 147425821173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1941 : Bounds (41252851 / 250000000) (33002281 / 200000000) (Real.log (147425821173 / 125000000000)) := by
  have h := reflection_log_1941_neg
  have he : Real.log (147425821173 / 125000000000) = -Real.log (125000000000 / 147425821173) := by
    rw [show ((147425821173 / 125000000000) : ℝ) = ((125000000000 / 147425821173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1942_neg : (82722173 / 500000000) ≤ -Real.log (500000000000 / 589958646969) ∧
    -Real.log (500000000000 / 589958646969) ≤ (165444347 / 1000000000) := by
  have h := checkLog_sound (w := (89958646969 / 1089958646969)) (n := 12)
    (lo := (82722173 / 500000000)) (hi := (165444347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589958646969 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589958646969 / 500000000000) = 1/(500000000000 / 589958646969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1942 : Bounds (82722173 / 500000000) (165444347 / 1000000000) (Real.log (589958646969 / 500000000000)) := by
  have h := reflection_log_1942_neg
  have he : Real.log (589958646969 / 500000000000) = -Real.log (500000000000 / 589958646969) := by
    rw [show ((589958646969 / 500000000000) : ℝ) = ((500000000000 / 589958646969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1943_neg : (66197803 / 200000000) ≤ -Real.log (500000000000 / 696172248803) ∧
    -Real.log (500000000000 / 696172248803) ≤ (41373627 / 125000000) := by
  have h := checkLog_sound (w := (196172248803 / 1196172248803)) (n := 12)
    (lo := (66197803 / 200000000)) (hi := (41373627 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696172248803 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696172248803 / 500000000000) = 1/(500000000000 / 696172248803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1943 : Bounds (66197803 / 200000000) (41373627 / 125000000) (Real.log (696172248803 / 500000000000)) := by
  have h := reflection_log_1943_neg
  have he : Real.log (696172248803 / 500000000000) = -Real.log (500000000000 / 696172248803) := by
    rw [show ((696172248803 / 500000000000) : ℝ) = ((500000000000 / 696172248803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1944_neg : (165597273 / 500000000) ≤ -Real.log (250000000000 / 348157674363) ∧
    -Real.log (250000000000 / 348157674363) ≤ (331194547 / 1000000000) := by
  have h := checkLog_sound (w := (98157674363 / 598157674363)) (n := 12)
    (lo := (165597273 / 500000000)) (hi := (331194547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((348157674363 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(348157674363 / 250000000000) = 1/(250000000000 / 348157674363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1944 : Bounds (165597273 / 500000000) (331194547 / 1000000000) (Real.log (348157674363 / 250000000000)) := by
  have h := reflection_log_1944_neg
  have he : Real.log (348157674363 / 250000000000) = -Real.log (250000000000 / 348157674363) := by
    rw [show ((348157674363 / 250000000000) : ℝ) = ((250000000000 / 348157674363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1945_neg : (30406831 / 200000000) ≤ -Real.log (5000 / 5821) ∧
    -Real.log (5000 / 5821) ≤ (38008539 / 250000000) := by
  have h := checkLog_sound (w := (821 / 10821)) (n := 12)
    (lo := (30406831 / 200000000)) (hi := (38008539 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5821 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5821 / 5000) = 1/(5000 / 5821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1945 : Bounds (30406831 / 200000000) (38008539 / 250000000) (Real.log (5821 / 5000)) := by
  have h := reflection_log_1945_neg
  have he : Real.log (5821 / 5000) = -Real.log (5000 / 5821) := by
    rw [show ((5821 / 5000) : ℝ) = ((5000 / 5821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1946_neg : (22420741 / 125000000) ≤ -Real.log (4179 / 5000) ∧
    -Real.log (4179 / 5000) ≤ (179365929 / 1000000000) := by
  have h := checkLog_sound (w := (821 / 9179)) (n := 12)
    (lo := (22420741 / 125000000)) (hi := (179365929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4179) = 1/(4179 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1946 : Bounds (-179365929 / 1000000000) (-22420741 / 125000000) (Real.log (4179 / 5000)) := by
  have h := reflection_log_1946_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1947_neg : (82093 / 500000000) ≤ -Real.log (5000000 / 5000821) ∧
    -Real.log (5000000 / 5000821) ≤ (164187 / 1000000000) := by
  have h := checkLog_sound (w := (821 / 10000821)) (n := 12)
    (lo := (82093 / 500000000)) (hi := (164187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000821 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000821 / 5000000) = 1/(5000000 / 5000821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1947 : Bounds (82093 / 500000000) (164187 / 1000000000) (Real.log (5000821 / 5000000)) := by
  have h := reflection_log_1947_neg
  have he : Real.log (5000821 / 5000000) = -Real.log (5000000 / 5000821) := by
    rw [show ((5000821 / 5000000) : ℝ) = ((5000000 / 5000821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1948_neg : (164213 / 1000000000) ≤ -Real.log (4999179 / 5000000) ∧
    -Real.log (4999179 / 5000000) ≤ (82107 / 500000000) := by
  have h := checkLog_sound (w := (821 / 9999179)) (n := 12)
    (lo := (164213 / 1000000000)) (hi := (82107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999179) = 1/(4999179 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1948 : Bounds (-82107 / 500000000) (-164213 / 1000000000) (Real.log (4999179 / 5000000)) := by
  have h := reflection_log_1948_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1949_neg : (79152157 / 1000000000) ≤ -Real.log (1000000 / 1082369) ∧
    -Real.log (1000000 / 1082369) ≤ (39576079 / 500000000) := by
  have h := checkLog_sound (w := (82369 / 2082369)) (n := 12)
    (lo := (79152157 / 1000000000)) (hi := (39576079 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082369 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082369 / 1000000) = 1/(1000000 / 1082369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1949 : Bounds (79152157 / 1000000000) (39576079 / 500000000) (Real.log (1082369 / 1000000)) := by
  have h := reflection_log_1949_neg
  have he : Real.log (1082369 / 1000000) = -Real.log (1000000 / 1082369) := by
    rw [show ((1082369 / 1000000) : ℝ) = ((1000000 / 1082369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1950_neg : (85959929 / 1000000000) ≤ -Real.log (917631 / 1000000) ∧
    -Real.log (917631 / 1000000) ≤ (8595993 / 100000000) := by
  have h := checkLog_sound (w := (82369 / 1917631)) (n := 12)
    (lo := (85959929 / 1000000000)) (hi := (8595993 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917631) = 1/(917631 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1950 : Bounds (-8595993 / 100000000) (-85959929 / 1000000000) (Real.log (917631 / 1000000)) := by
  have h := reflection_log_1950_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1951_neg : (79351699 / 1000000000) ≤ -Real.log (200000 / 216517) ∧
    -Real.log (200000 / 216517) ≤ (793517 / 10000000) := by
  have h := checkLog_sound (w := (16517 / 416517)) (n := 12)
    (lo := (79351699 / 1000000000)) (hi := (793517 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216517 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216517 / 200000) = 1/(200000 / 216517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1951 : Bounds (79351699 / 1000000000) (793517 / 10000000) (Real.log (216517 / 200000)) := by
  have h := reflection_log_1951_neg
  have he : Real.log (216517 / 200000) = -Real.log (200000 / 216517) := by
    rw [show ((216517 / 200000) : ℝ) = ((200000 / 216517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1952_neg : (43097673 / 500000000) ≤ -Real.log (183483 / 200000) ∧
    -Real.log (183483 / 200000) ≤ (86195347 / 1000000000) := by
  have h := checkLog_sound (w := (16517 / 383483)) (n := 12)
    (lo := (43097673 / 500000000)) (hi := (86195347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183483) = 1/(183483 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1952 : Bounds (-86195347 / 1000000000) (-43097673 / 500000000) (Real.log (183483 / 200000)) := by
  have h := reflection_log_1952_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1953_neg : (3421823 / 500000000) ≤ -Real.log (39727188711 / 40000000000) ∧
    -Real.log (39727188711 / 40000000000) ≤ (6843647 / 1000000000) := by
  have h := checkLog_sound (w := (272811289 / 79727188711)) (n := 12)
    (lo := (3421823 / 500000000)) (hi := (6843647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39727188711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39727188711) = 1/(39727188711 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1953 : Bounds (-6843647 / 1000000000) (-3421823 / 500000000) (Real.log (39727188711 / 40000000000)) := by
  have h := reflection_log_1953_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1954_neg : (1701943 / 250000000) ≤ -Real.log (993215347839 / 1000000000000) ∧
    -Real.log (993215347839 / 1000000000000) ≤ (6807773 / 1000000000) := by
  have h := checkLog_sound (w := (6784652161 / 1993215347839)) (n := 12)
    (lo := (1701943 / 250000000)) (hi := (6807773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993215347839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993215347839) = 1/(993215347839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1954 : Bounds (-6807773 / 1000000000) (-1701943 / 250000000) (Real.log (993215347839 / 1000000000000)) := by
  have h := reflection_log_1954_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1955_neg : (165112087 / 1000000000) ≤ -Real.log (50000000000 / 58976266059) ∧
    -Real.log (50000000000 / 58976266059) ≤ (20639011 / 125000000) := by
  have h := checkLog_sound (w := (8976266059 / 108976266059)) (n := 12)
    (lo := (165112087 / 1000000000)) (hi := (20639011 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58976266059 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58976266059 / 50000000000) = 1/(50000000000 / 58976266059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1955 : Bounds (165112087 / 1000000000) (20639011 / 125000000) (Real.log (58976266059 / 50000000000)) := by
  have h := reflection_log_1955_neg
  have he : Real.log (58976266059 / 50000000000) = -Real.log (50000000000 / 58976266059) := by
    rw [show ((58976266059 / 50000000000) : ℝ) = ((50000000000 / 58976266059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1956_neg : (82773523 / 500000000) ≤ -Real.log (12500000000 / 14750480971) ∧
    -Real.log (12500000000 / 14750480971) ≤ (165547047 / 1000000000) := by
  have h := checkLog_sound (w := (2250480971 / 27250480971)) (n := 12)
    (lo := (82773523 / 500000000)) (hi := (165547047 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14750480971 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14750480971 / 12500000000) = 1/(12500000000 / 14750480971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1956 : Bounds (82773523 / 500000000) (165547047 / 1000000000) (Real.log (14750480971 / 12500000000)) := by
  have h := reflection_log_1956_neg
  have he : Real.log (14750480971 / 12500000000) = -Real.log (12500000000 / 14750480971) := by
    rw [show ((14750480971 / 12500000000) : ℝ) = ((12500000000 / 14750480971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1957_neg : (165597273 / 500000000) ≤ -Real.log (20000000000 / 27852613949) ∧
    -Real.log (20000000000 / 27852613949) ≤ (331194547 / 1000000000) := by
  have h := checkLog_sound (w := (7852613949 / 47852613949)) (n := 12)
    (lo := (165597273 / 500000000)) (hi := (331194547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27852613949 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27852613949 / 20000000000) = 1/(20000000000 / 27852613949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1957 : Bounds (165597273 / 500000000) (331194547 / 1000000000) (Real.log (27852613949 / 20000000000)) := by
  have h := reflection_log_1957_neg
  have he : Real.log (27852613949 / 20000000000) = -Real.log (20000000000 / 27852613949) := by
    rw [show ((27852613949 / 20000000000) : ℝ) = ((20000000000 / 27852613949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1958_neg : (82850021 / 250000000) ≤ -Real.log (500000000000 / 696458482891) ∧
    -Real.log (500000000000 / 696458482891) ≤ (66280017 / 200000000) := by
  have h := checkLog_sound (w := (196458482891 / 1196458482891)) (n := 12)
    (lo := (82850021 / 250000000)) (hi := (66280017 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696458482891 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696458482891 / 500000000000) = 1/(500000000000 / 696458482891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1958 : Bounds (82850021 / 250000000) (66280017 / 200000000) (Real.log (696458482891 / 500000000000)) := by
  have h := reflection_log_1958_neg
  have he : Real.log (696458482891 / 500000000000) = -Real.log (500000000000 / 696458482891) := by
    rw [show ((696458482891 / 500000000000) : ℝ) = ((500000000000 / 696458482891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1959_neg : (9507503 / 62500000) ≤ -Real.log (10000 / 11643) ∧
    -Real.log (10000 / 11643) ≤ (152120049 / 1000000000) := by
  have h := checkLog_sound (w := (1643 / 21643)) (n := 12)
    (lo := (9507503 / 62500000)) (hi := (152120049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11643 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11643 / 10000) = 1/(10000 / 11643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1959 : Bounds (9507503 / 62500000) (152120049 / 1000000000) (Real.log (11643 / 10000)) := by
  have h := reflection_log_1959_neg
  have he : Real.log (11643 / 10000) = -Real.log (10000 / 11643) := by
    rw [show ((11643 / 10000) : ℝ) = ((10000 / 11643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1960_neg : (179485581 / 1000000000) ≤ -Real.log (8357 / 10000) ∧
    -Real.log (8357 / 10000) ≤ (89742791 / 500000000) := by
  have h := checkLog_sound (w := (1643 / 18357)) (n := 12)
    (lo := (179485581 / 1000000000)) (hi := (89742791 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8357) = 1/(8357 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1960 : Bounds (-89742791 / 500000000) (-179485581 / 1000000000) (Real.log (8357 / 10000)) := by
  have h := reflection_log_1960_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1961_neg : (82143 / 500000000) ≤ -Real.log (10000000 / 10001643) ∧
    -Real.log (10000000 / 10001643) ≤ (164287 / 1000000000) := by
  have h := checkLog_sound (w := (1643 / 20001643)) (n := 12)
    (lo := (82143 / 500000000)) (hi := (164287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001643 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001643 / 10000000) = 1/(10000000 / 10001643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1961 : Bounds (82143 / 500000000) (164287 / 1000000000) (Real.log (10001643 / 10000000)) := by
  have h := reflection_log_1961_neg
  have he : Real.log (10001643 / 10000000) = -Real.log (10000000 / 10001643) := by
    rw [show ((10001643 / 10000000) : ℝ) = ((10000000 / 10001643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1962_neg : (164313 / 1000000000) ≤ -Real.log (9998357 / 10000000) ∧
    -Real.log (9998357 / 10000000) ≤ (82157 / 500000000) := by
  have h := checkLog_sound (w := (1643 / 19998357)) (n := 12)
    (lo := (164313 / 1000000000)) (hi := (82157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998357) = 1/(9998357 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1962 : Bounds (-82157 / 500000000) (-164313 / 1000000000) (Real.log (9998357 / 10000000)) := by
  have h := reflection_log_1962_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1963_neg : (3167971 / 40000000) ≤ -Real.log (50000 / 54121) ∧
    -Real.log (50000 / 54121) ≤ (19799819 / 250000000) := by
  have h := checkLog_sound (w := (4121 / 104121)) (n := 12)
    (lo := (3167971 / 40000000)) (hi := (19799819 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54121 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54121 / 50000) = 1/(50000 / 54121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1963 : Bounds (3167971 / 40000000) (19799819 / 250000000) (Real.log (54121 / 50000)) := by
  have h := reflection_log_1963_neg
  have he : Real.log (54121 / 50000) = -Real.log (50000 / 54121) := by
    rw [show ((54121 / 50000) : ℝ) = ((50000 / 54121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1964_neg : (86015509 / 1000000000) ≤ -Real.log (45879 / 50000) ∧
    -Real.log (45879 / 50000) ≤ (8601551 / 100000000) := by
  have h := checkLog_sound (w := (4121 / 95879)) (n := 12)
    (lo := (86015509 / 1000000000)) (hi := (8601551 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45879) = 1/(45879 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1964 : Bounds (-8601551 / 100000000) (-86015509 / 1000000000) (Real.log (45879 / 50000)) := by
  have h := reflection_log_1964_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1965_neg : (19849471 / 250000000) ≤ -Real.log (200000 / 216527) ∧
    -Real.log (200000 / 216527) ≤ (15879577 / 200000000) := by
  have h := checkLog_sound (w := (16527 / 416527)) (n := 12)
    (lo := (19849471 / 250000000)) (hi := (15879577 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216527 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216527 / 200000) = 1/(200000 / 216527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1965 : Bounds (19849471 / 250000000) (15879577 / 200000000) (Real.log (216527 / 200000)) := by
  have h := reflection_log_1965_neg
  have he : Real.log (216527 / 200000) = -Real.log (200000 / 216527) := by
    rw [show ((216527 / 200000) : ℝ) = ((200000 / 216527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1966_neg : (10781231 / 125000000) ≤ -Real.log (183473 / 200000) ∧
    -Real.log (183473 / 200000) ≤ (86249849 / 1000000000) := by
  have h := checkLog_sound (w := (16527 / 383473)) (n := 12)
    (lo := (10781231 / 125000000)) (hi := (86249849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183473) = 1/(183473 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1966 : Bounds (-86249849 / 1000000000) (-10781231 / 125000000) (Real.log (183473 / 200000)) := by
  have h := reflection_log_1966_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1967_neg : (1712991 / 250000000) ≤ -Real.log (39726858271 / 40000000000) ∧
    -Real.log (39726858271 / 40000000000) ≤ (1370393 / 200000000) := by
  have h := checkLog_sound (w := (273141729 / 79726858271)) (n := 12)
    (lo := (1712991 / 250000000)) (hi := (1370393 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39726858271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39726858271) = 1/(39726858271 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1967 : Bounds (-1370393 / 200000000) (-1712991 / 250000000) (Real.log (39726858271 / 40000000000)) := by
  have h := reflection_log_1967_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1968_neg : (3408117 / 500000000) ≤ -Real.log (2483017359 / 2500000000) ∧
    -Real.log (2483017359 / 2500000000) ≤ (1363247 / 200000000) := by
  have h := checkLog_sound (w := (16982641 / 4983017359)) (n := 12)
    (lo := (3408117 / 500000000)) (hi := (1363247 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2483017359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2483017359) = 1/(2483017359 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1968 : Bounds (-1363247 / 200000000) (-3408117 / 500000000) (Real.log (2483017359 / 2500000000)) := by
  have h := reflection_log_1968_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1969_neg : (2581481 / 15625000) ≤ -Real.log (500000000000 / 589823230671) ∧
    -Real.log (500000000000 / 589823230671) ≤ (33042957 / 200000000) := by
  have h := checkLog_sound (w := (89823230671 / 1089823230671)) (n := 12)
    (lo := (2581481 / 15625000)) (hi := (33042957 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589823230671 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589823230671 / 500000000000) = 1/(500000000000 / 589823230671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1969 : Bounds (2581481 / 15625000) (33042957 / 200000000) (Real.log (589823230671 / 500000000000)) := by
  have h := reflection_log_1969_neg
  have he : Real.log (589823230671 / 500000000000) = -Real.log (500000000000 / 589823230671) := by
    rw [show ((589823230671 / 500000000000) : ℝ) = ((500000000000 / 589823230671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1970_neg : (165647733 / 1000000000) ≤ -Real.log (20000000000 / 23603145967) ∧
    -Real.log (20000000000 / 23603145967) ≤ (82823867 / 500000000) := by
  have h := checkLog_sound (w := (3603145967 / 43603145967)) (n := 12)
    (lo := (165647733 / 1000000000)) (hi := (82823867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23603145967 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23603145967 / 20000000000) = 1/(20000000000 / 23603145967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1970 : Bounds (165647733 / 1000000000) (82823867 / 500000000) (Real.log (23603145967 / 20000000000)) := by
  have h := reflection_log_1970_neg
  have he : Real.log (23603145967 / 20000000000) = -Real.log (20000000000 / 23603145967) := by
    rw [show ((23603145967 / 20000000000) : ℝ) = ((20000000000 / 23603145967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1971_neg : (82850021 / 250000000) ≤ -Real.log (50000000000 / 69645848289) ∧
    -Real.log (50000000000 / 69645848289) ≤ (66280017 / 200000000) := by
  have h := checkLog_sound (w := (19645848289 / 119645848289)) (n := 12)
    (lo := (82850021 / 250000000)) (hi := (66280017 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69645848289 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69645848289 / 50000000000) = 1/(50000000000 / 69645848289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1971 : Bounds (82850021 / 250000000) (66280017 / 200000000) (Real.log (69645848289 / 50000000000)) := by
  have h := reflection_log_1971_neg
  have he : Real.log (69645848289 / 50000000000) = -Real.log (50000000000 / 69645848289) := by
    rw [show ((69645848289 / 50000000000) : ℝ) = ((50000000000 / 69645848289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1972_neg : (33160563 / 100000000) ≤ -Real.log (500000000000 / 696601651311) ∧
    -Real.log (500000000000 / 696601651311) ≤ (331605631 / 1000000000) := by
  have h := checkLog_sound (w := (196601651311 / 1196601651311)) (n := 12)
    (lo := (33160563 / 100000000)) (hi := (331605631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((696601651311 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(696601651311 / 500000000000) = 1/(500000000000 / 696601651311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1972 : Bounds (33160563 / 100000000) (331605631 / 1000000000) (Real.log (696601651311 / 500000000000)) := by
  have h := reflection_log_1972_neg
  have he : Real.log (696601651311 / 500000000000) = -Real.log (500000000000 / 696601651311) := by
    rw [show ((696601651311 / 500000000000) : ℝ) = ((500000000000 / 696601651311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1973_neg : (38051483 / 250000000) ≤ -Real.log (2500 / 2911) ∧
    -Real.log (2500 / 2911) ≤ (152205933 / 1000000000) := by
  have h := checkLog_sound (w := (411 / 5411)) (n := 12)
    (lo := (38051483 / 250000000)) (hi := (152205933 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2911 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2911 / 2500) = 1/(2500 / 2911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1973 : Bounds (38051483 / 250000000) (152205933 / 1000000000) (Real.log (2911 / 2500)) := by
  have h := reflection_log_1973_neg
  have he : Real.log (2911 / 2500) = -Real.log (2500 / 2911) := by
    rw [show ((2911 / 2500) : ℝ) = ((2500 / 2911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1974_neg : (179605249 / 1000000000) ≤ -Real.log (2089 / 2500) ∧
    -Real.log (2089 / 2500) ≤ (718421 / 4000000) := by
  have h := checkLog_sound (w := (411 / 4589)) (n := 12)
    (lo := (179605249 / 1000000000)) (hi := (718421 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2089) = 1/(2089 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1974 : Bounds (-718421 / 4000000) (-179605249 / 1000000000) (Real.log (2089 / 2500)) := by
  have h := reflection_log_1974_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1975_neg : (82193 / 500000000) ≤ -Real.log (2500000 / 2500411) ∧
    -Real.log (2500000 / 2500411) ≤ (164387 / 1000000000) := by
  have h := checkLog_sound (w := (411 / 5000411)) (n := 12)
    (lo := (82193 / 500000000)) (hi := (164387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500411 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500411 / 2500000) = 1/(2500000 / 2500411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1975 : Bounds (82193 / 500000000) (164387 / 1000000000) (Real.log (2500411 / 2500000)) := by
  have h := reflection_log_1975_neg
  have he : Real.log (2500411 / 2500000) = -Real.log (2500000 / 2500411) := by
    rw [show ((2500411 / 2500000) : ℝ) = ((2500000 / 2500411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1976_neg : (164413 / 1000000000) ≤ -Real.log (2499589 / 2500000) ∧
    -Real.log (2499589 / 2500000) ≤ (82207 / 500000000) := by
  have h := checkLog_sound (w := (411 / 4999589)) (n := 12)
    (lo := (164413 / 1000000000)) (hi := (82207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499589) = 1/(2499589 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1976 : Bounds (-82207 / 500000000) (-164413 / 1000000000) (Real.log (2499589 / 2500000)) := by
  have h := reflection_log_1976_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1977_neg : (7924639 / 100000000) ≤ -Real.log (1000000 / 1082471) ∧
    -Real.log (1000000 / 1082471) ≤ (79246391 / 1000000000) := by
  have h := checkLog_sound (w := (82471 / 2082471)) (n := 12)
    (lo := (7924639 / 100000000)) (hi := (79246391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1082471 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1082471 / 1000000) = 1/(1000000 / 1082471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1977 : Bounds (7924639 / 100000000) (79246391 / 1000000000) (Real.log (1082471 / 1000000)) := by
  have h := reflection_log_1977_neg
  have he : Real.log (1082471 / 1000000) = -Real.log (1000000 / 1082471) := by
    rw [show ((1082471 / 1000000) : ℝ) = ((1000000 / 1082471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1978_neg : (86071091 / 1000000000) ≤ -Real.log (917529 / 1000000) ∧
    -Real.log (917529 / 1000000) ≤ (21517773 / 250000000) := by
  have h := checkLog_sound (w := (82471 / 1917529)) (n := 12)
    (lo := (86071091 / 1000000000)) (hi := (21517773 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 917529) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 917529) = 1/(917529 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1978 : Bounds (-21517773 / 250000000) (-86071091 / 1000000000) (Real.log (917529 / 1000000)) := by
  have h := reflection_log_1978_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1979_neg : (7944499 / 100000000) ≤ -Real.log (500000 / 541343) ∧
    -Real.log (500000 / 541343) ≤ (79444991 / 1000000000) := by
  have h := checkLog_sound (w := (41343 / 1041343)) (n := 12)
    (lo := (7944499 / 100000000)) (hi := (79444991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541343 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541343 / 500000) = 1/(500000 / 541343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1979 : Bounds (7944499 / 100000000) (79444991 / 1000000000) (Real.log (541343 / 500000)) := by
  have h := reflection_log_1979_neg
  have he : Real.log (541343 / 500000) = -Real.log (500000 / 541343) := by
    rw [show ((541343 / 500000) : ℝ) = ((500000 / 541343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1980_neg : (21576361 / 250000000) ≤ -Real.log (458657 / 500000) ∧
    -Real.log (458657 / 500000) ≤ (17261089 / 200000000) := by
  have h := checkLog_sound (w := (41343 / 958657)) (n := 12)
    (lo := (21576361 / 250000000)) (hi := (17261089 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458657) = 1/(458657 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1980 : Bounds (-17261089 / 200000000) (-21576361 / 250000000) (Real.log (458657 / 500000)) := by
  have h := reflection_log_1980_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1981_neg : (6860453 / 1000000000) ≤ -Real.log (248290756351 / 250000000000) ∧
    -Real.log (248290756351 / 250000000000) ≤ (3430227 / 500000000) := by
  have h := checkLog_sound (w := (1709243649 / 498290756351)) (n := 12)
    (lo := (6860453 / 1000000000)) (hi := (3430227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248290756351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248290756351) = 1/(248290756351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1981 : Bounds (-3430227 / 500000000) (-6860453 / 1000000000) (Real.log (248290756351 / 250000000000)) := by
  have h := reflection_log_1981_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1982_neg : (6824701 / 1000000000) ≤ -Real.log (993198534159 / 1000000000000) ∧
    -Real.log (993198534159 / 1000000000000) ≤ (3412351 / 500000000) := by
  have h := checkLog_sound (w := (6801465841 / 1993198534159)) (n := 12)
    (lo := (6824701 / 1000000000)) (hi := (3412351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993198534159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993198534159) = 1/(993198534159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1982 : Bounds (-3412351 / 500000000) (-6824701 / 1000000000) (Real.log (993198534159 / 1000000000000)) := by
  have h := reflection_log_1982_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1983_neg : (82658741 / 500000000) ≤ -Real.log (500000000000 / 589883807487) ∧
    -Real.log (500000000000 / 589883807487) ≤ (165317483 / 1000000000) := by
  have h := checkLog_sound (w := (89883807487 / 1089883807487)) (n := 12)
    (lo := (82658741 / 500000000)) (hi := (165317483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589883807487 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589883807487 / 500000000000) = 1/(500000000000 / 589883807487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1983 : Bounds (82658741 / 500000000) (165317483 / 1000000000) (Real.log (589883807487 / 500000000000)) := by
  have h := reflection_log_1983_neg
  have he : Real.log (589883807487 / 500000000000) = -Real.log (500000000000 / 589883807487) := by
    rw [show ((589883807487 / 500000000000) : ℝ) = ((500000000000 / 589883807487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
