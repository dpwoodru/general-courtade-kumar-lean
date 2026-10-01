import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell168
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

theorem reflection_log_1_neg : (299380951 / 1000000000) ≤ -Real.log (5120 / 6907) ∧
    -Real.log (5120 / 6907) ≤ (37422619 / 125000000) := by
  have h := checkLog_sound (w := (1787 / 12027)) (n := 12)
    (lo := (299380951 / 1000000000)) (hi := (37422619 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6907 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6907 / 5120) = 1/(5120 / 6907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (299380951 / 1000000000) (37422619 / 125000000) (Real.log (6907 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6907 / 5120) = -Real.log (5120 / 6907) := by
    rw [show ((6907 / 5120) : ℝ) = ((5120 / 6907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (429281639 / 1000000000) ≤ -Real.log (3333 / 5120) ∧
    -Real.log (3333 / 5120) ≤ (10732041 / 25000000) := by
  have h := checkLog_sound (w := (1787 / 8453)) (n := 12)
    (lo := (429281639 / 1000000000)) (hi := (10732041 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3333) = 1/(3333 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-10732041 / 25000000) (-429281639 / 1000000000) (Real.log (3333 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (149473257 / 500000000) ≤ -Real.log (640 / 863) ∧
    -Real.log (640 / 863) ≤ (59789303 / 200000000) := by
  have h := checkLog_sound (w := (223 / 1503)) (n := 12)
    (lo := (149473257 / 500000000)) (hi := (59789303 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((863 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(863 / 640) = 1/(640 / 863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (149473257 / 500000000) (59789303 / 200000000) (Real.log (863 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (863 / 640) = -Real.log (640 / 863) := by
    rw [show ((863 / 640) : ℝ) = ((640 / 863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (214190977 / 500000000) ≤ -Real.log (417 / 640) ∧
    -Real.log (417 / 640) ≤ (85676391 / 200000000) := by
  have h := checkLog_sound (w := (223 / 1057)) (n := 12)
    (lo := (214190977 / 500000000)) (hi := (85676391 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 417) = 1/(417 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-85676391 / 200000000) (-214190977 / 500000000) (Real.log (417 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (221297849 / 1000000000) ≤ -Real.log (200000 / 249539) ∧
    -Real.log (200000 / 249539) ≤ (4425957 / 20000000) := by
  have h := checkLog_sound (w := (49539 / 449539)) (n := 12)
    (lo := (221297849 / 1000000000)) (hi := (4425957 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249539 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(249539 / 200000) = 1/(200000 / 249539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (221297849 / 1000000000) (4425957 / 20000000) (Real.log (249539 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (249539 / 200000) = -Real.log (200000 / 249539) := by
    rw [show ((249539 / 200000) : ℝ) = ((200000 / 249539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (71153363 / 250000000) ≤ -Real.log (150461 / 200000) ∧
    -Real.log (150461 / 200000) ≤ (284613453 / 1000000000) := by
  have h := checkLog_sound (w := (49539 / 350461)) (n := 12)
    (lo := (71153363 / 250000000)) (hi := (284613453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 150461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 150461) = 1/(150461 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-284613453 / 1000000000) (-71153363 / 250000000) (Real.log (150461 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (13852301 / 62500000) ≤ -Real.log (500000 / 624059) ∧
    -Real.log (500000 / 624059) ≤ (221636817 / 1000000000) := by
  have h := checkLog_sound (w := (124059 / 1124059)) (n := 12)
    (lo := (13852301 / 62500000)) (hi := (221636817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((624059 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(624059 / 500000) = 1/(500000 / 624059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (13852301 / 62500000) (221636817 / 1000000000) (Real.log (624059 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (624059 / 500000) = -Real.log (500000 / 624059) := by
    rw [show ((624059 / 500000) : ℝ) = ((500000 / 624059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (142587941 / 500000000) ≤ -Real.log (375941 / 500000) ∧
    -Real.log (375941 / 500000) ≤ (285175883 / 1000000000) := by
  have h := checkLog_sound (w := (124059 / 875941)) (n := 12)
    (lo := (142587941 / 500000000)) (hi := (285175883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 375941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 375941) = 1/(375941 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-285175883 / 1000000000) (-142587941 / 500000000) (Real.log (375941 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (163966631 / 1000000000) ≤ -Real.log (40000 / 47127) ∧
    -Real.log (40000 / 47127) ≤ (20495829 / 125000000) := by
  have h := checkLog_sound (w := (7127 / 87127)) (n := 12)
    (lo := (163966631 / 1000000000)) (hi := (20495829 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47127 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47127 / 40000) = 1/(40000 / 47127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (163966631 / 1000000000) (20495829 / 125000000) (Real.log (47127 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (47127 / 40000) = -Real.log (40000 / 47127) := by
    rw [show ((47127 / 40000) : ℝ) = ((40000 / 47127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (196227801 / 1000000000) ≤ -Real.log (32873 / 40000) ∧
    -Real.log (32873 / 40000) ≤ (98113901 / 500000000) := by
  have h := checkLog_sound (w := (7127 / 72873)) (n := 12)
    (lo := (196227801 / 1000000000)) (hi := (98113901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 32873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 32873) = 1/(32873 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-98113901 / 500000000) (-196227801 / 1000000000) (Real.log (32873 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (164233957 / 1000000000) ≤ -Real.log (100000 / 117849) ∧
    -Real.log (100000 / 117849) ≤ (82116979 / 500000000) := by
  have h := checkLog_sound (w := (17849 / 217849)) (n := 12)
    (lo := (164233957 / 1000000000)) (hi := (82116979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117849 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117849 / 100000) = 1/(100000 / 117849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (164233957 / 1000000000) (82116979 / 500000000) (Real.log (117849 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (117849 / 100000) = -Real.log (100000 / 117849) := by
    rw [show ((117849 / 100000) : ℝ) = ((100000 / 117849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (6144099 / 31250000) ≤ -Real.log (82151 / 100000) ∧
    -Real.log (82151 / 100000) ≤ (196611169 / 1000000000) := by
  have h := checkLog_sound (w := (17849 / 182151)) (n := 12)
    (lo := (6144099 / 31250000)) (hi := (196611169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 82151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 82151) = 1/(82151 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-196611169 / 1000000000) (-6144099 / 31250000) (Real.log (82151 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (181832117 / 250000000) ≤ -Real.log (250000000000 / 517386091127) ∧
    -Real.log (250000000000 / 517386091127) ≤ (72732847 / 100000000) := by
  have h := checkLog_sound (w := (17386091127 / 1017386091127)) (n := 12)
    (lo := (4272661 / 125000000)) (hi := (34181289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((517386091127 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(517386091127 / 500000000000) = 1/(250000000000 / 517386091127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (181832117 / 250000000) (72732847 / 100000000) (Real.log (517386091127 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (517386091127 / 250000000000) = -Real.log (250000000000 / 517386091127) := by
    rw [show ((517386091127 / 250000000000) : ℝ) = ((250000000000 / 517386091127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (72866259 / 100000000) ≤ -Real.log (250000000000 / 518076807681) ∧
    -Real.log (250000000000 / 518076807681) ≤ (11385353 / 15625000) := by
  have h := checkLog_sound (w := (18076807681 / 1018076807681)) (n := 12)
    (lo := (3551541 / 100000000)) (hi := (35515411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((518076807681 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(518076807681 / 500000000000) = 1/(250000000000 / 518076807681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (72866259 / 100000000) (11385353 / 15625000) (Real.log (518076807681 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (518076807681 / 250000000000) = -Real.log (250000000000 / 518076807681) := by
    rw [show ((518076807681 / 250000000000) : ℝ) = ((250000000000 / 518076807681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (505911301 / 1000000000) ≤ -Real.log (250000000000 / 414624055403) ∧
    -Real.log (250000000000 / 414624055403) ≤ (252955651 / 500000000) := by
  have h := checkLog_sound (w := (164624055403 / 664624055403)) (n := 12)
    (lo := (505911301 / 1000000000)) (hi := (252955651 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((414624055403 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(414624055403 / 250000000000) = 1/(250000000000 / 414624055403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (505911301 / 1000000000) (252955651 / 500000000) (Real.log (414624055403 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (414624055403 / 250000000000) = -Real.log (250000000000 / 414624055403) := by
    rw [show ((414624055403 / 250000000000) : ℝ) = ((250000000000 / 414624055403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (253406349 / 500000000) ≤ -Real.log (500000000000 / 829995930213) ∧
    -Real.log (500000000000 / 829995930213) ≤ (506812699 / 1000000000) := by
  have h := checkLog_sound (w := (329995930213 / 1329995930213)) (n := 12)
    (lo := (253406349 / 500000000)) (hi := (506812699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((829995930213 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(829995930213 / 500000000000) = 1/(500000000000 / 829995930213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (253406349 / 500000000) (506812699 / 1000000000) (Real.log (829995930213 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (829995930213 / 500000000000) = -Real.log (500000000000 / 829995930213) := by
    rw [show ((829995930213 / 500000000000) : ℝ) = ((500000000000 / 829995930213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (360194433 / 1000000000) ≤ -Real.log (4000000000 / 5734432513) ∧
    -Real.log (4000000000 / 5734432513) ≤ (180097217 / 500000000) := by
  have h := checkLog_sound (w := (1734432513 / 9734432513)) (n := 12)
    (lo := (360194433 / 1000000000)) (hi := (180097217 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5734432513 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5734432513 / 4000000000) = 1/(4000000000 / 5734432513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (360194433 / 1000000000) (180097217 / 500000000) (Real.log (5734432513 / 4000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5734432513 / 4000000000) = -Real.log (4000000000 / 5734432513) := by
    rw [show ((5734432513 / 4000000000) : ℝ) = ((4000000000 / 5734432513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (180422563 / 500000000) ≤ -Real.log (500000000000 / 717270635781) ∧
    -Real.log (500000000000 / 717270635781) ≤ (360845127 / 1000000000) := by
  have h := checkLog_sound (w := (217270635781 / 1217270635781)) (n := 12)
    (lo := (180422563 / 500000000)) (hi := (360845127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717270635781 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717270635781 / 500000000000) = 1/(500000000000 / 717270635781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (180422563 / 500000000) (360845127 / 1000000000) (Real.log (717270635781 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (717270635781 / 500000000000) = -Real.log (500000000000 / 717270635781) := by
    rw [show ((717270635781 / 500000000000) : ℝ) = ((500000000000 / 717270635781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3237721 / 100000000) ≤ -Real.log (9681413199 / 10000000000) ∧
    -Real.log (9681413199 / 10000000000) ≤ (32377211 / 1000000000) := by
  have h := checkLog_sound (w := (318586801 / 19681413199)) (n := 12)
    (lo := (3237721 / 100000000)) (hi := (32377211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9681413199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9681413199) = 1/(9681413199 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-32377211 / 1000000000) (-3237721 / 100000000) (Real.log (9681413199 / 10000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (3226117 / 100000000) ≤ -Real.log (1549205871 / 1600000000) ∧
    -Real.log (1549205871 / 1600000000) ≤ (32261171 / 1000000000) := by
  have h := checkLog_sound (w := (50794129 / 3149205871)) (n := 12)
    (lo := (3226117 / 100000000)) (hi := (32261171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1549205871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1549205871) = 1/(1549205871 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-32261171 / 1000000000) (-3226117 / 100000000) (Real.log (1549205871 / 1600000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell168
