import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell039
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (1888437 / 7812500) ≤ -Real.log (128 / 163) ∧
    -Real.log (128 / 163) ≤ (241719937 / 1000000000) := by
  have h := checkLog_sound (w := (35 / 291)) (n := 12)
    (lo := (1888437 / 7812500)) (hi := (241719937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163 / 128) = 1/(128 / 163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (1888437 / 7812500) (241719937 / 1000000000) (Real.log (163 / 128)) := by
  have h := reflection_log_1_neg
  have he : Real.log (163 / 128) = -Real.log (128 / 163) := by
    rw [show ((163 / 128) : ℝ) = ((128 / 163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (31943077 / 100000000) ≤ -Real.log (93 / 128) ∧
    -Real.log (93 / 128) ≤ (319430771 / 1000000000) := by
  have h := checkLog_sound (w := (35 / 221)) (n := 12)
    (lo := (31943077 / 100000000)) (hi := (319430771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128 / 93) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(128 / 93) = 1/(93 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-319430771 / 1000000000) (-31943077 / 100000000) (Real.log (93 / 128)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (60314927 / 250000000) ≤ -Real.log (5120 / 6517) ∧
    -Real.log (5120 / 6517) ≤ (241259709 / 1000000000) := by
  have h := checkLog_sound (w := (1397 / 11637)) (n := 12)
    (lo := (60314927 / 250000000)) (hi := (241259709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6517 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6517 / 5120) = 1/(5120 / 6517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (60314927 / 250000000) (241259709 / 1000000000) (Real.log (6517 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6517 / 5120) = -Real.log (5120 / 6517) := by
    rw [show ((6517 / 5120) : ℝ) = ((5120 / 6517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (79656161 / 250000000) ≤ -Real.log (3723 / 5120) ∧
    -Real.log (3723 / 5120) ≤ (63724929 / 200000000) := by
  have h := checkLog_sound (w := (1397 / 8843)) (n := 12)
    (lo := (79656161 / 250000000)) (hi := (63724929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3723) = 1/(3723 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-63724929 / 200000000) (-79656161 / 250000000) (Real.log (3723 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (35386747 / 200000000) ≤ -Real.log (62500 / 74597) ∧
    -Real.log (62500 / 74597) ≤ (22116717 / 125000000) := by
  have h := checkLog_sound (w := (12097 / 137097)) (n := 12)
    (lo := (35386747 / 200000000)) (hi := (22116717 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74597 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74597 / 62500) = 1/(62500 / 74597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (35386747 / 200000000) (22116717 / 125000000) (Real.log (74597 / 62500)) := by
  have h := reflection_log_5_neg
  have he : Real.log (74597 / 62500) = -Real.log (62500 / 74597) := by
    rw [show ((74597 / 62500) : ℝ) = ((62500 / 74597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (215115859 / 1000000000) ≤ -Real.log (50403 / 62500) ∧
    -Real.log (50403 / 62500) ≤ (10755793 / 50000000) := by
  have h := checkLog_sound (w := (12097 / 112903)) (n := 12)
    (lo := (215115859 / 1000000000)) (hi := (10755793 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 50403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 50403) = 1/(50403 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-10755793 / 50000000) (-215115859 / 1000000000) (Real.log (50403 / 62500)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (44321391 / 250000000) ≤ -Real.log (250000 / 298493) ∧
    -Real.log (250000 / 298493) ≤ (35457113 / 200000000) := by
  have h := checkLog_sound (w := (48493 / 548493)) (n := 12)
    (lo := (44321391 / 250000000)) (hi := (35457113 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298493 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298493 / 250000) = 1/(250000 / 298493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (44321391 / 250000000) (35457113 / 200000000) (Real.log (298493 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (298493 / 250000) = -Real.log (250000 / 298493) := by
    rw [show ((298493 / 250000) : ℝ) = ((250000 / 298493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (215636797 / 1000000000) ≤ -Real.log (201507 / 250000) ∧
    -Real.log (201507 / 250000) ≤ (107818399 / 500000000) := by
  have h := checkLog_sound (w := (48493 / 451507)) (n := 12)
    (lo := (215636797 / 1000000000)) (hi := (107818399 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 201507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 201507) = 1/(201507 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-107818399 / 500000000) (-215636797 / 1000000000) (Real.log (201507 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (32383541 / 250000000) ≤ -Real.log (500000 / 569149) ∧
    -Real.log (500000 / 569149) ≤ (25906833 / 200000000) := by
  have h := checkLog_sound (w := (69149 / 1069149)) (n := 12)
    (lo := (32383541 / 250000000)) (hi := (25906833 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((569149 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(569149 / 500000) = 1/(500000 / 569149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (32383541 / 250000000) (25906833 / 200000000) (Real.log (569149 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (569149 / 500000) = -Real.log (500000 / 569149) := by
    rw [show ((569149 / 500000) : ℝ) = ((500000 / 569149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (5953831 / 40000000) ≤ -Real.log (430851 / 500000) ∧
    -Real.log (430851 / 500000) ≤ (9302861 / 62500000) := by
  have h := checkLog_sound (w := (69149 / 930851)) (n := 12)
    (lo := (5953831 / 40000000)) (hi := (9302861 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 430851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 430851) = 1/(430851 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-9302861 / 62500000) (-5953831 / 40000000) (Real.log (430851 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (2596059 / 20000000) ≤ -Real.log (250000 / 284651) ∧
    -Real.log (250000 / 284651) ≤ (129802951 / 1000000000) := by
  have h := checkLog_sound (w := (34651 / 534651)) (n := 12)
    (lo := (2596059 / 20000000)) (hi := (129802951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((284651 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(284651 / 250000) = 1/(250000 / 284651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (2596059 / 20000000) (129802951 / 1000000000) (Real.log (284651 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (284651 / 250000) = -Real.log (250000 / 284651) := by
    rw [show ((284651 / 250000) : ℝ) = ((250000 / 284651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (149200949 / 1000000000) ≤ -Real.log (215349 / 250000) ∧
    -Real.log (215349 / 250000) ≤ (2984019 / 20000000) := by
  have h := checkLog_sound (w := (34651 / 465349)) (n := 12)
    (lo := (149200949 / 1000000000)) (hi := (2984019 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 215349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 215349) = 1/(215349 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2984019 / 20000000) (-149200949 / 1000000000) (Real.log (215349 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (8748193 / 15625000) ≤ -Real.log (500000000000 / 875235025517) ∧
    -Real.log (500000000000 / 875235025517) ≤ (559884353 / 1000000000) := by
  have h := checkLog_sound (w := (375235025517 / 1375235025517)) (n := 12)
    (lo := (8748193 / 15625000)) (hi := (559884353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((875235025517 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(875235025517 / 500000000000) = 1/(500000000000 / 875235025517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (8748193 / 15625000) (559884353 / 1000000000) (Real.log (875235025517 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (875235025517 / 500000000000) = -Real.log (500000000000 / 875235025517) := by
    rw [show ((875235025517 / 500000000000) : ℝ) = ((500000000000 / 875235025517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (561150707 / 1000000000) ≤ -Real.log (250000000000 / 438172043011) ∧
    -Real.log (250000000000 / 438172043011) ≤ (140287677 / 250000000) := by
  have h := checkLog_sound (w := (188172043011 / 688172043011)) (n := 12)
    (lo := (561150707 / 1000000000)) (hi := (140287677 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((438172043011 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(438172043011 / 250000000000) = 1/(250000000000 / 438172043011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (561150707 / 1000000000) (140287677 / 250000000) (Real.log (438172043011 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (438172043011 / 250000000000) = -Real.log (250000000000 / 438172043011) := by
    rw [show ((438172043011 / 250000000000) : ℝ) = ((250000000000 / 438172043011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (196024797 / 500000000) ≤ -Real.log (62500000000 / 92500694403) ∧
    -Real.log (62500000000 / 92500694403) ≤ (78409919 / 200000000) := by
  have h := checkLog_sound (w := (30000694403 / 155000694403)) (n := 12)
    (lo := (196024797 / 500000000)) (hi := (78409919 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((92500694403 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(92500694403 / 62500000000) = 1/(62500000000 / 92500694403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (196024797 / 500000000) (78409919 / 200000000) (Real.log (92500694403 / 62500000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (92500694403 / 62500000000) = -Real.log (62500000000 / 92500694403) := by
    rw [show ((92500694403 / 62500000000) : ℝ) = ((62500000000 / 92500694403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (392922361 / 1000000000) ≤ -Real.log (6250000000 / 9258146119) ∧
    -Real.log (6250000000 / 9258146119) ≤ (196461181 / 500000000) := by
  have h := checkLog_sound (w := (3008146119 / 15508146119)) (n := 12)
    (lo := (392922361 / 1000000000)) (hi := (196461181 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9258146119 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9258146119 / 6250000000) = 1/(6250000000 / 9258146119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (392922361 / 1000000000) (196461181 / 500000000) (Real.log (9258146119 / 6250000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (9258146119 / 6250000000) = -Real.log (6250000000 / 9258146119) := by
    rw [show ((9258146119 / 6250000000) : ℝ) = ((6250000000 / 9258146119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (13918997 / 50000000) ≤ -Real.log (100000000000 / 132098799817) ∧
    -Real.log (100000000000 / 132098799817) ≤ (278379941 / 1000000000) := by
  have h := checkLog_sound (w := (32098799817 / 232098799817)) (n := 12)
    (lo := (13918997 / 50000000)) (hi := (278379941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((132098799817 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(132098799817 / 100000000000) = 1/(100000000000 / 132098799817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (13918997 / 50000000) (278379941 / 1000000000) (Real.log (132098799817 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (132098799817 / 100000000000) = -Real.log (100000000000 / 132098799817) := by
    rw [show ((132098799817 / 100000000000) : ℝ) = ((100000000000 / 132098799817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2790039 / 10000000) ≤ -Real.log (100000000000 / 132181249971) ∧
    -Real.log (100000000000 / 132181249971) ≤ (279003901 / 1000000000) := by
  have h := checkLog_sound (w := (32181249971 / 232181249971)) (n := 12)
    (lo := (2790039 / 10000000)) (hi := (279003901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((132181249971 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(132181249971 / 100000000000) = 1/(100000000000 / 132181249971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2790039 / 10000000) (279003901 / 1000000000) (Real.log (132181249971 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (132181249971 / 100000000000) = -Real.log (100000000000 / 132181249971) := by
    rw [show ((132181249971 / 100000000000) : ℝ) = ((100000000000 / 132181249971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (19397999 / 1000000000) ≤ -Real.log (61299308199 / 62500000000) ∧
    -Real.log (61299308199 / 62500000000) ≤ (9699 / 500000) := by
  have h := checkLog_sound (w := (1200691801 / 123799308199)) (n := 12)
    (lo := (19397999 / 1000000000)) (hi := (9699 / 500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61299308199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61299308199) = 1/(61299308199 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-9699 / 500000) (-19397999 / 1000000000) (Real.log (61299308199 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (19311611 / 1000000000) ≤ -Real.log (245218415799 / 250000000000) ∧
    -Real.log (245218415799 / 250000000000) ≤ (4827903 / 250000000) := by
  have h := checkLog_sound (w := (4781584201 / 495218415799)) (n := 12)
    (lo := (19311611 / 1000000000)) (hi := (4827903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 245218415799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 245218415799) = 1/(245218415799 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4827903 / 250000000) (-19311611 / 1000000000) (Real.log (245218415799 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell039
