import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell107
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

theorem reflection_log_1_neg : (34066097 / 125000000) ≤ -Real.log (1280 / 1681) ∧
    -Real.log (1280 / 1681) ≤ (272528777 / 1000000000) := by
  have h := checkLog_sound (w := (401 / 2961)) (n := 12)
    (lo := (34066097 / 125000000)) (hi := (272528777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1681 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1681 / 1280) = 1/(1280 / 1681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (34066097 / 125000000) (272528777 / 1000000000) (Real.log (1681 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1681 / 1280) = -Real.log (1280 / 1681) := by
    rw [show ((1681 / 1280) : ℝ) = ((1280 / 1681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (375830459 / 1000000000) ≤ -Real.log (879 / 1280) ∧
    -Real.log (879 / 1280) ≤ (18791523 / 50000000) := by
  have h := checkLog_sound (w := (401 / 2159)) (n := 12)
    (lo := (375830459 / 1000000000)) (hi := (18791523 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 879) = 1/(879 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-18791523 / 50000000) (-375830459 / 1000000000) (Real.log (879 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (272082513 / 1000000000) ≤ -Real.log (5120 / 6721) ∧
    -Real.log (5120 / 6721) ≤ (136041257 / 500000000) := by
  have h := checkLog_sound (w := (1601 / 11841)) (n := 12)
    (lo := (272082513 / 1000000000)) (hi := (136041257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6721 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6721 / 5120) = 1/(5120 / 6721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (272082513 / 1000000000) (136041257 / 500000000) (Real.log (6721 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6721 / 5120) = -Real.log (5120 / 6721) := by
    rw [show ((6721 / 5120) : ℝ) = ((5120 / 6721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (18748879 / 50000000) ≤ -Real.log (3519 / 5120) ∧
    -Real.log (3519 / 5120) ≤ (374977581 / 1000000000) := by
  have h := checkLog_sound (w := (1601 / 8639)) (n := 12)
    (lo := (18748879 / 50000000)) (hi := (374977581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3519) = 1/(3519 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-374977581 / 1000000000) (-18748879 / 50000000) (Real.log (3519 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (200528139 / 1000000000) ≤ -Real.log (31250 / 38189) ∧
    -Real.log (31250 / 38189) ≤ (10026407 / 50000000) := by
  have h := checkLog_sound (w := (6939 / 69439)) (n := 12)
    (lo := (200528139 / 1000000000)) (hi := (10026407 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38189 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38189 / 31250) = 1/(31250 / 38189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (200528139 / 1000000000) (10026407 / 50000000) (Real.log (38189 / 31250)) := by
  have h := reflection_log_5_neg
  have he : Real.log (38189 / 31250) = -Real.log (31250 / 38189) := by
    rw [show ((38189 / 31250) : ℝ) = ((31250 / 38189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (251090453 / 1000000000) ≤ -Real.log (24311 / 31250) ∧
    -Real.log (24311 / 31250) ≤ (125545227 / 500000000) := by
  have h := checkLog_sound (w := (6939 / 55561)) (n := 12)
    (lo := (251090453 / 1000000000)) (hi := (125545227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 24311) = 1/(24311 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-125545227 / 500000000) (-251090453 / 1000000000) (Real.log (24311 / 31250)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (25109073 / 125000000) ≤ -Real.log (1000000 / 1222469) ∧
    -Real.log (1000000 / 1222469) ≤ (40174517 / 200000000) := by
  have h := checkLog_sound (w := (222469 / 2222469)) (n := 12)
    (lo := (25109073 / 125000000)) (hi := (40174517 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1222469 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1222469 / 1000000) = 1/(1000000 / 1222469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (25109073 / 125000000) (40174517 / 200000000) (Real.log (1222469 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1222469 / 1000000) = -Real.log (1000000 / 1222469) := by
    rw [show ((1222469 / 1000000) : ℝ) = ((1000000 / 1222469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (62907941 / 250000000) ≤ -Real.log (777531 / 1000000) ∧
    -Real.log (777531 / 1000000) ≤ (50326353 / 200000000) := by
  have h := checkLog_sound (w := (222469 / 1777531)) (n := 12)
    (lo := (62907941 / 250000000)) (hi := (50326353 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 777531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 777531) = 1/(777531 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-50326353 / 200000000) (-62907941 / 250000000) (Real.log (777531 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (73859017 / 500000000) ≤ -Real.log (500000 / 579593) ∧
    -Real.log (500000 / 579593) ≤ (29543607 / 200000000) := by
  have h := checkLog_sound (w := (79593 / 1079593)) (n := 12)
    (lo := (73859017 / 500000000)) (hi := (29543607 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((579593 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(579593 / 500000) = 1/(500000 / 579593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (73859017 / 500000000) (29543607 / 200000000) (Real.log (579593 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (579593 / 500000) = -Real.log (500000 / 579593) := by
    rw [show ((579593 / 500000) : ℝ) = ((500000 / 579593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (21673101 / 125000000) ≤ -Real.log (420407 / 500000) ∧
    -Real.log (420407 / 500000) ≤ (173384809 / 1000000000) := by
  have h := checkLog_sound (w := (79593 / 920407)) (n := 12)
    (lo := (21673101 / 125000000)) (hi := (173384809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 420407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 420407) = 1/(420407 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-173384809 / 1000000000) (-21673101 / 125000000) (Real.log (420407 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (147985427 / 1000000000) ≤ -Real.log (125000 / 144937) ∧
    -Real.log (125000 / 144937) ≤ (36996357 / 250000000) := by
  have h := checkLog_sound (w := (19937 / 269937)) (n := 12)
    (lo := (147985427 / 1000000000)) (hi := (36996357 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((144937 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(144937 / 125000) = 1/(125000 / 144937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (147985427 / 1000000000) (36996357 / 250000000) (Real.log (144937 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (144937 / 125000) = -Real.log (125000 / 144937) := by
    rw [show ((144937 / 125000) : ℝ) = ((125000 / 144937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (173753567 / 1000000000) ≤ -Real.log (105063 / 125000) ∧
    -Real.log (105063 / 125000) ≤ (5429799 / 31250000) := by
  have h := checkLog_sound (w := (19937 / 230063)) (n := 12)
    (lo := (173753567 / 1000000000)) (hi := (5429799 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 105063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 105063) = 1/(105063 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-5429799 / 31250000) (-173753567 / 1000000000) (Real.log (105063 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (323530047 / 500000000) ≤ -Real.log (62500000000 / 119369849389) ∧
    -Real.log (62500000000 / 119369849389) ≤ (129412019 / 200000000) := by
  have h := checkLog_sound (w := (56869849389 / 181869849389)) (n := 12)
    (lo := (323530047 / 500000000)) (hi := (129412019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119369849389 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119369849389 / 62500000000) = 1/(62500000000 / 119369849389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (323530047 / 500000000) (129412019 / 200000000) (Real.log (119369849389 / 62500000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (119369849389 / 62500000000) = -Real.log (62500000000 / 119369849389) := by
    rw [show ((119369849389 / 62500000000) : ℝ) = ((62500000000 / 119369849389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (129671847 / 200000000) ≤ -Real.log (125000000000 / 239050056883) ∧
    -Real.log (125000000000 / 239050056883) ≤ (162089809 / 250000000) := by
  have h := checkLog_sound (w := (114050056883 / 364050056883)) (n := 12)
    (lo := (129671847 / 200000000)) (hi := (162089809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((239050056883 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(239050056883 / 125000000000) = 1/(125000000000 / 239050056883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (129671847 / 200000000) (162089809 / 250000000) (Real.log (239050056883 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (239050056883 / 125000000000) = -Real.log (125000000000 / 239050056883) := by
    rw [show ((239050056883 / 125000000000) : ℝ) = ((125000000000 / 239050056883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (451618593 / 1000000000) ≤ -Real.log (500000000000 / 785426350211) ∧
    -Real.log (500000000000 / 785426350211) ≤ (225809297 / 500000000) := by
  have h := checkLog_sound (w := (285426350211 / 1285426350211)) (n := 12)
    (lo := (451618593 / 1000000000)) (hi := (225809297 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((785426350211 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(785426350211 / 500000000000) = 1/(500000000000 / 785426350211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (451618593 / 1000000000) (225809297 / 500000000) (Real.log (785426350211 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (785426350211 / 500000000000) = -Real.log (500000000000 / 785426350211) := by
    rw [show ((785426350211 / 500000000000) : ℝ) = ((500000000000 / 785426350211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (113126087 / 250000000) ≤ -Real.log (100000000000 / 157224470793) ∧
    -Real.log (100000000000 / 157224470793) ≤ (452504349 / 1000000000) := by
  have h := checkLog_sound (w := (57224470793 / 257224470793)) (n := 12)
    (lo := (113126087 / 250000000)) (hi := (452504349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157224470793 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157224470793 / 100000000000) = 1/(100000000000 / 157224470793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (113126087 / 250000000) (452504349 / 1000000000) (Real.log (157224470793 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (157224470793 / 100000000000) = -Real.log (100000000000 / 157224470793) := by
    rw [show ((157224470793 / 100000000000) : ℝ) = ((100000000000 / 157224470793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (321102843 / 1000000000) ≤ -Real.log (125000000000 / 172330919799) ∧
    -Real.log (125000000000 / 172330919799) ≤ (80275711 / 250000000) := by
  have h := checkLog_sound (w := (47330919799 / 297330919799)) (n := 12)
    (lo := (321102843 / 1000000000)) (hi := (80275711 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172330919799 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172330919799 / 125000000000) = 1/(125000000000 / 172330919799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (321102843 / 1000000000) (80275711 / 250000000) (Real.log (172330919799 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (172330919799 / 125000000000) = -Real.log (125000000000 / 172330919799) := by
    rw [show ((172330919799 / 125000000000) : ℝ) = ((125000000000 / 172330919799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (64347799 / 200000000) ≤ -Real.log (500000000000 / 689762333077) ∧
    -Real.log (500000000000 / 689762333077) ≤ (80434749 / 250000000) := by
  have h := checkLog_sound (w := (189762333077 / 1189762333077)) (n := 12)
    (lo := (64347799 / 200000000)) (hi := (80434749 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((689762333077 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(689762333077 / 500000000000) = 1/(500000000000 / 689762333077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (64347799 / 200000000) (80434749 / 250000000) (Real.log (689762333077 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (689762333077 / 500000000000) = -Real.log (500000000000 / 689762333077) := by
    rw [show ((689762333077 / 500000000000) : ℝ) = ((500000000000 / 689762333077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (25768139 / 1000000000) ≤ -Real.log (15227516031 / 15625000000) ∧
    -Real.log (15227516031 / 15625000000) ≤ (1288407 / 50000000) := by
  have h := checkLog_sound (w := (397483969 / 30852516031)) (n := 12)
    (lo := (25768139 / 1000000000)) (hi := (1288407 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15227516031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15227516031) = 1/(15227516031 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-1288407 / 50000000) (-25768139 / 1000000000) (Real.log (15227516031 / 15625000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (12833387 / 500000000) ≤ -Real.log (243664954351 / 250000000000) ∧
    -Real.log (243664954351 / 250000000000) ≤ (1026671 / 40000000) := by
  have h := checkLog_sound (w := (6335045649 / 493664954351)) (n := 12)
    (lo := (12833387 / 500000000)) (hi := (1026671 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243664954351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243664954351) = 1/(243664954351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1026671 / 40000000) (-12833387 / 500000000) (Real.log (243664954351 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell107
