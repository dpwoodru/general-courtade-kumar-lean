import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0091
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

theorem reflection_log_1_neg : (336556931 / 500000000) ≤ -Real.log (51200 / 100369) ∧
    -Real.log (51200 / 100369) ≤ (673113863 / 1000000000) := by
  have h := checkLog_sound (w := (49169 / 151569)) (n := 12)
    (lo := (336556931 / 500000000)) (hi := (673113863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100369 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100369 / 51200) = 1/(51200 / 100369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (336556931 / 500000000) (673113863 / 1000000000) (Real.log (100369 / 51200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (100369 / 51200) = -Real.log (51200 / 100369) := by
    rw [show ((100369 / 51200) : ℝ) = ((51200 / 100369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3227211247 / 1000000000) ≤ -Real.log (2031 / 51200) ∧
    -Real.log (2031 / 51200) ≤ (806802813 / 250000000) := by
  have h := checkLog_sound (w := (1169 / 5231)) (n := 12)
    (lo := (454622527 / 1000000000)) (hi := (7103477 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2031) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2031) = 1/(2031 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-806802813 / 250000000) (-3227211247 / 1000000000) (Real.log (2031 / 51200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (672924543 / 1000000000) ≤ -Real.log (1024 / 2007) ∧
    -Real.log (1024 / 2007) ≤ (5257223 / 7812500) := by
  have h := checkLog_sound (w := (983 / 3031)) (n := 12)
    (lo := (672924543 / 1000000000)) (hi := (5257223 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2007 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2007 / 1024) = 1/(1024 / 2007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (672924543 / 1000000000) (5257223 / 7812500) (Real.log (2007 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2007 / 1024) = -Real.log (1024 / 2007) := by
    rw [show ((2007 / 1024) : ℝ) = ((1024 / 2007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (402237467 / 125000000) ≤ -Real.log (41 / 1024) ∧
    -Real.log (41 / 1024) ≤ (3217899741 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 105)) (n := 12)
    (lo := (55663877 / 125000000)) (hi := (445311017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 41) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(64 / 41) = 1/(41 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3217899741 / 1000000000) (-402237467 / 125000000) (Real.log (41 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (40791937 / 62500000) ≤ -Real.log (25600 / 49169) ∧
    -Real.log (25600 / 49169) ≤ (652670993 / 1000000000) := by
  have h := checkLog_sound (w := (23569 / 74769)) (n := 12)
    (lo := (40791937 / 62500000)) (hi := (652670993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49169 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49169 / 25600) = 1/(25600 / 49169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (40791937 / 62500000) (652670993 / 1000000000) (Real.log (49169 / 25600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (49169 / 25600) = -Real.log (25600 / 49169) := by
    rw [show ((49169 / 25600) : ℝ) = ((25600 / 49169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2534064067 / 1000000000) ≤ -Real.log (2031 / 25600) ∧
    -Real.log (2031 / 25600) ≤ (2534064071 / 1000000000) := by
  have h := checkLog_sound (w := (1169 / 5231)) (n := 12)
    (lo := (454622527 / 1000000000)) (hi := (7103477 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2031) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3200 / 2031) = 1/(2031 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2534064071 / 1000000000) (-2534064067 / 1000000000) (Real.log (2031 / 25600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (130456899 / 200000000) ≤ -Real.log (512 / 983) ∧
    -Real.log (512 / 983) ≤ (40767781 / 62500000) := by
  have h := checkLog_sound (w := (471 / 1495)) (n := 12)
    (lo := (130456899 / 200000000)) (hi := (40767781 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983 / 512) = 1/(512 / 983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (130456899 / 200000000) (40767781 / 62500000) (Real.log (983 / 512)) := by
  have h := reflection_log_7_neg
  have he : Real.log (983 / 512) = -Real.log (512 / 983) := by
    rw [show ((983 / 512) : ℝ) = ((512 / 983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (631188139 / 250000000) ≤ -Real.log (41 / 512) ∧
    -Real.log (41 / 512) ≤ (31559407 / 12500000) := by
  have h := checkLog_sound (w := (23 / 105)) (n := 12)
    (lo := (55663877 / 125000000)) (hi := (445311017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 41) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(64 / 41) = 1/(41 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-31559407 / 12500000) (-631188139 / 250000000) (Real.log (41 / 512)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (676522249 / 1000000000) ≤ -Real.log (40000 / 78681) ∧
    -Real.log (40000 / 78681) ≤ (2706089 / 4000000) := by
  have h := checkLog_sound (w := (38681 / 118681)) (n := 12)
    (lo := (676522249 / 1000000000)) (hi := (2706089 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78681 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78681 / 40000) = 1/(40000 / 78681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (676522249 / 1000000000) (2706089 / 4000000) (Real.log (78681 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (78681 / 40000) = -Real.log (40000 / 78681) := by
    rw [show ((78681 / 40000) : ℝ) = ((40000 / 78681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1706002789 / 500000000) ≤ -Real.log (1319 / 40000) ∧
    -Real.log (1319 / 40000) ≤ (3412005583 / 1000000000) := by
  have h := checkLog_sound (w := (1181 / 3819)) (n := 12)
    (lo := (319708429 / 500000000)) (hi := (639416859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 1319) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2500 / 1319) = 1/(1319 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3412005583 / 1000000000) (-1706002789 / 500000000) (Real.log (1319 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (16916729 / 25000000) ≤ -Real.log (500000 / 983657) ∧
    -Real.log (500000 / 983657) ≤ (676669161 / 1000000000) := by
  have h := checkLog_sound (w := (483657 / 1483657)) (n := 12)
    (lo := (16916729 / 25000000)) (hi := (676669161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983657 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983657 / 500000) = 1/(500000 / 983657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (16916729 / 25000000) (676669161 / 1000000000) (Real.log (983657 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (983657 / 500000) = -Real.log (500000 / 983657) := by
    rw [show ((983657 / 500000) : ℝ) = ((500000 / 983657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (136832337 / 40000000) ≤ -Real.log (16343 / 500000) ∧
    -Real.log (16343 / 500000) ≤ (342080843 / 100000000) := by
  have h := checkLog_sound (w := (14907 / 47593)) (n := 12)
    (lo := (129643941 / 200000000)) (hi := (324109853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16343) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 16343) = 1/(16343 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-342080843 / 100000000) (-136832337 / 40000000) (Real.log (16343 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (338187149 / 500000000) ≤ -Real.log (500000 / 983367) ∧
    -Real.log (500000 / 983367) ≤ (676374299 / 1000000000) := by
  have h := checkLog_sound (w := (483367 / 1483367)) (n := 12)
    (lo := (338187149 / 500000000)) (hi := (676374299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983367 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983367 / 500000) = 1/(500000 / 983367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (338187149 / 500000000) (676374299 / 1000000000) (Real.log (983367 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (983367 / 500000) = -Real.log (500000 / 983367) := by
    rw [show ((983367 / 500000) : ℝ) = ((500000 / 983367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1701609711 / 500000000) ≤ -Real.log (16633 / 500000) ∧
    -Real.log (16633 / 500000) ≤ (3403219427 / 1000000000) := by
  have h := checkLog_sound (w := (14617 / 47883)) (n := 12)
    (lo := (315315351 / 500000000)) (hi := (630630703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 16633) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 16633) = 1/(16633 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3403219427 / 1000000000) (-1701609711 / 500000000) (Real.log (16633 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (67652479 / 100000000) ≤ -Real.log (100000 / 196703) ∧
    -Real.log (100000 / 196703) ≤ (676524791 / 1000000000) := by
  have h := checkLog_sound (w := (96703 / 296703)) (n := 12)
    (lo := (67652479 / 100000000)) (hi := (676524791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((196703 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(196703 / 100000) = 1/(100000 / 196703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (67652479 / 100000000) (676524791 / 1000000000) (Real.log (196703 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (196703 / 100000) = -Real.log (100000 / 196703) := by
    rw [show ((196703 / 100000) : ℝ) = ((100000 / 196703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3412157219 / 1000000000) ≤ -Real.log (3297 / 100000) ∧
    -Real.log (3297 / 100000) ≤ (426519653 / 125000000) := by
  have h := checkLog_sound (w := (2953 / 9547)) (n := 12)
    (lo := (639568499 / 1000000000)) (hi := (1279137 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3297) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(6250 / 3297) = 1/(3297 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-426519653 / 125000000) (-3412157219 / 1000000000) (Real.log (3297 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2044263913 / 500000000) ≤ -Real.log (5000000000 / 298260045489) ∧
    -Real.log (5000000000 / 298260045489) ≤ (511065979 / 125000000) := by
  have h := checkLog_sound (w := (138260045489 / 458260045489)) (n := 12)
    (lo := (311395963 / 500000000)) (hi := (622791927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298260045489 / 160000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(298260045489 / 160000000000) = 1/(5000000000 / 298260045489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2044263913 / 500000000) (511065979 / 125000000) (Real.log (298260045489 / 5000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (298260045489 / 5000000000) = -Real.log (5000000000 / 298260045489) := by
    rw [show ((298260045489 / 5000000000) : ℝ) = ((5000000000 / 298260045489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (819495517 / 200000000) ≤ -Real.log (62500000000 / 3761767270391) ∧
    -Real.log (62500000000 / 3761767270391) ≤ (4097477591 / 1000000000) := by
  have h := checkLog_sound (w := (1761767270391 / 5761767270391)) (n := 12)
    (lo := (126348337 / 200000000)) (hi := (315870843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3761767270391 / 2000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3761767270391 / 2000000000000) = 1/(62500000000 / 3761767270391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (819495517 / 200000000) (4097477591 / 1000000000) (Real.log (3761767270391 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3761767270391 / 62500000000) = -Real.log (62500000000 / 3761767270391) := by
    rw [show ((3761767270391 / 62500000000) : ℝ) = ((62500000000 / 3761767270391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (101989843 / 25000000) ≤ -Real.log (125000000000 / 7390180664943) ∧
    -Real.log (125000000000 / 7390180664943) ≤ (2039796863 / 500000000) := by
  have h := checkLog_sound (w := (3390180664943 / 11390180664943)) (n := 12)
    (lo := (30692891 / 50000000)) (hi := (613857821 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7390180664943 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(7390180664943 / 4000000000000) = 1/(125000000000 / 7390180664943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (101989843 / 25000000) (2039796863 / 500000000) (Real.log (7390180664943 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (7390180664943 / 125000000000) = -Real.log (125000000000 / 7390180664943) := by
    rw [show ((7390180664943 / 125000000000) : ℝ) = ((125000000000 / 7390180664943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (408868201 / 100000000) ≤ -Real.log (125000000000 / 7457650894753) ∧
    -Real.log (125000000000 / 7457650894753) ≤ (127771313 / 31250000) := by
  have h := checkLog_sound (w := (3457650894753 / 11457650894753)) (n := 12)
    (lo := (62294611 / 100000000)) (hi := (622946111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7457650894753 / 4000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(7457650894753 / 4000000000000) = 1/(125000000000 / 7457650894753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (408868201 / 100000000) (127771313 / 31250000) (Real.log (7457650894753 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7457650894753 / 125000000000) = -Real.log (125000000000 / 7457650894753) := by
    rw [show ((7457650894753 / 125000000000) : ℝ) = ((125000000000 / 7457650894753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0091
