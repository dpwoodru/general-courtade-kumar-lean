import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell179
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

theorem reflection_log_1_neg : (60829467 / 200000000) ≤ -Real.log (256 / 347) ∧
    -Real.log (256 / 347) ≤ (38018417 / 125000000) := by
  have h := checkLog_sound (w := (91 / 603)) (n := 12)
    (lo := (60829467 / 200000000)) (hi := (38018417 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((347 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(347 / 256) = 1/(256 / 347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (60829467 / 200000000) (38018417 / 125000000) (Real.log (347 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (347 / 256) = -Real.log (256 / 347) := by
    rw [show ((347 / 256) : ℝ) = ((256 / 347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (43923197 / 100000000) ≤ -Real.log (165 / 256) ∧
    -Real.log (165 / 256) ≤ (439231971 / 1000000000) := by
  have h := checkLog_sound (w := (91 / 421)) (n := 12)
    (lo := (43923197 / 100000000)) (hi := (439231971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 165) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 165) = 1/(165 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-439231971 / 1000000000) (-43923197 / 100000000) (Real.log (165 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (60742993 / 200000000) ≤ -Real.log (5120 / 6937) ∧
    -Real.log (5120 / 6937) ≤ (151857483 / 500000000) := by
  have h := checkLog_sound (w := (1817 / 12057)) (n := 12)
    (lo := (60742993 / 200000000)) (hi := (151857483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6937 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6937 / 5120) = 1/(5120 / 6937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (60742993 / 200000000) (151857483 / 500000000) (Real.log (6937 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6937 / 5120) = -Real.log (5120 / 6937) := by
    rw [show ((6937 / 5120) : ℝ) = ((5120 / 6937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (109580823 / 250000000) ≤ -Real.log (3303 / 5120) ∧
    -Real.log (3303 / 5120) ≤ (438323293 / 1000000000) := by
  have h := checkLog_sound (w := (1817 / 8423)) (n := 12)
    (lo := (109580823 / 250000000)) (hi := (438323293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3303) = 1/(3303 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-438323293 / 1000000000) (-109580823 / 250000000) (Real.log (3303 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (28125727 / 125000000) ≤ -Real.log (100000 / 125233) ∧
    -Real.log (100000 / 125233) ≤ (225005817 / 1000000000) := by
  have h := checkLog_sound (w := (25233 / 225233)) (n := 12)
    (lo := (28125727 / 125000000)) (hi := (225005817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125233 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125233 / 100000) = 1/(100000 / 125233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (28125727 / 125000000) (225005817 / 1000000000) (Real.log (125233 / 100000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (125233 / 100000) = -Real.log (100000 / 125233) := by
    rw [show ((125233 / 100000) : ℝ) = ((100000 / 125233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (145396787 / 500000000) ≤ -Real.log (74767 / 100000) ∧
    -Real.log (74767 / 100000) ≤ (11631743 / 40000000) := by
  have h := checkLog_sound (w := (25233 / 174767)) (n := 12)
    (lo := (145396787 / 500000000)) (hi := (11631743 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 74767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 74767) = 1/(74767 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-11631743 / 40000000) (-145396787 / 500000000) (Real.log (74767 / 100000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (225342731 / 1000000000) ≤ -Real.log (62500 / 78297) ∧
    -Real.log (62500 / 78297) ≤ (56335683 / 250000000) := by
  have h := checkLog_sound (w := (15797 / 140797)) (n := 12)
    (lo := (225342731 / 1000000000)) (hi := (56335683 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78297 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78297 / 62500) = 1/(62500 / 78297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (225342731 / 1000000000) (56335683 / 250000000) (Real.log (78297 / 62500)) := by
  have h := reflection_log_7_neg
  have he : Real.log (78297 / 62500) = -Real.log (62500 / 78297) := by
    rw [show ((78297 / 62500) : ℝ) = ((62500 / 78297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (145679077 / 500000000) ≤ -Real.log (46703 / 62500) ∧
    -Real.log (46703 / 62500) ≤ (58271631 / 200000000) := by
  have h := checkLog_sound (w := (15797 / 109203)) (n := 12)
    (lo := (145679077 / 500000000)) (hi := (58271631 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 46703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 46703) = 1/(46703 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-58271631 / 200000000) (-145679077 / 500000000) (Real.log (46703 / 62500)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (41723287 / 250000000) ≤ -Real.log (250000 / 295407) ∧
    -Real.log (250000 / 295407) ≤ (166893149 / 1000000000) := by
  have h := checkLog_sound (w := (45407 / 545407)) (n := 12)
    (lo := (41723287 / 250000000)) (hi := (166893149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295407 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295407 / 250000) = 1/(250000 / 295407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (41723287 / 250000000) (166893149 / 1000000000) (Real.log (295407 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (295407 / 250000) = -Real.log (250000 / 295407) := by
    rw [show ((295407 / 250000) : ℝ) = ((250000 / 295407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (100219139 / 500000000) ≤ -Real.log (204593 / 250000) ∧
    -Real.log (204593 / 250000) ≤ (200438279 / 1000000000) := by
  have h := checkLog_sound (w := (45407 / 454593)) (n := 12)
    (lo := (100219139 / 500000000)) (hi := (200438279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 204593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 204593) = 1/(204593 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-200438279 / 1000000000) (-100219139 / 500000000) (Real.log (204593 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (83579847 / 500000000) ≤ -Real.log (1000000 / 1181943) ∧
    -Real.log (1000000 / 1181943) ≤ (33431939 / 200000000) := by
  have h := checkLog_sound (w := (181943 / 2181943)) (n := 12)
    (lo := (83579847 / 500000000)) (hi := (33431939 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1181943 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1181943 / 1000000) = 1/(1000000 / 1181943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (83579847 / 500000000) (33431939 / 200000000) (Real.log (1181943 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1181943 / 1000000) = -Real.log (1000000 / 1181943) := by
    rw [show ((1181943 / 1000000) : ℝ) = ((1000000 / 1181943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (100411631 / 500000000) ≤ -Real.log (818057 / 1000000) ∧
    -Real.log (818057 / 1000000) ≤ (200823263 / 1000000000) := by
  have h := checkLog_sound (w := (181943 / 1818057)) (n := 12)
    (lo := (100411631 / 500000000)) (hi := (200823263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 818057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 818057) = 1/(818057 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-200823263 / 1000000000) (-100411631 / 500000000) (Real.log (818057 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (742038257 / 1000000000) ≤ -Real.log (250000000000 / 525052982137) ∧
    -Real.log (250000000000 / 525052982137) ≤ (742038259 / 1000000000) := by
  have h := checkLog_sound (w := (25052982137 / 1025052982137)) (n := 12)
    (lo := (48891077 / 1000000000)) (hi := (24445539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((525052982137 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(525052982137 / 500000000000) = 1/(250000000000 / 525052982137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (742038257 / 1000000000) (742038259 / 1000000000) (Real.log (525052982137 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (525052982137 / 250000000000) = -Real.log (250000000000 / 525052982137) := by
    rw [show ((525052982137 / 250000000000) : ℝ) = ((250000000000 / 525052982137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (148675861 / 200000000) ≤ -Real.log (125000000000 / 262878787879) ∧
    -Real.log (125000000000 / 262878787879) ≤ (743379307 / 1000000000) := by
  have h := checkLog_sound (w := (12878787879 / 512878787879)) (n := 12)
    (lo := (401857 / 8000000)) (hi := (25116063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((262878787879 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(262878787879 / 250000000000) = 1/(125000000000 / 262878787879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (148675861 / 200000000) (743379307 / 1000000000) (Real.log (262878787879 / 125000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (262878787879 / 125000000000) = -Real.log (125000000000 / 262878787879) := by
    rw [show ((262878787879 / 125000000000) : ℝ) = ((125000000000 / 262878787879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (515799391 / 1000000000) ≤ -Real.log (500000000000 / 837488464161) ∧
    -Real.log (500000000000 / 837488464161) ≤ (16118731 / 31250000) := by
  have h := checkLog_sound (w := (337488464161 / 1337488464161)) (n := 12)
    (lo := (515799391 / 1000000000)) (hi := (16118731 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((837488464161 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(837488464161 / 500000000000) = 1/(500000000000 / 837488464161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (515799391 / 1000000000) (16118731 / 31250000) (Real.log (837488464161 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (837488464161 / 500000000000) = -Real.log (500000000000 / 837488464161) := by
    rw [show ((837488464161 / 500000000000) : ℝ) = ((500000000000 / 837488464161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (103340177 / 200000000) ≤ -Real.log (250000000000 / 419121897951) ∧
    -Real.log (250000000000 / 419121897951) ≤ (258350443 / 500000000) := by
  have h := checkLog_sound (w := (169121897951 / 669121897951)) (n := 12)
    (lo := (103340177 / 200000000)) (hi := (258350443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((419121897951 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(419121897951 / 250000000000) = 1/(250000000000 / 419121897951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (103340177 / 200000000) (258350443 / 500000000) (Real.log (419121897951 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (419121897951 / 250000000000) = -Real.log (250000000000 / 419121897951) := by
    rw [show ((419121897951 / 250000000000) : ℝ) = ((250000000000 / 419121897951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (183665713 / 500000000) ≤ -Real.log (250000000000 / 360969094739) ∧
    -Real.log (250000000000 / 360969094739) ≤ (367331427 / 1000000000) := by
  have h := checkLog_sound (w := (110969094739 / 610969094739)) (n := 12)
    (lo := (183665713 / 500000000)) (hi := (367331427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((360969094739 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(360969094739 / 250000000000) = 1/(250000000000 / 360969094739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (183665713 / 500000000) (367331427 / 1000000000) (Real.log (360969094739 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (360969094739 / 250000000000) = -Real.log (250000000000 / 360969094739) := by
    rw [show ((360969094739 / 250000000000) : ℝ) = ((250000000000 / 360969094739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (367982957 / 1000000000) ≤ -Real.log (250000000000 / 361204353731) ∧
    -Real.log (250000000000 / 361204353731) ≤ (183991479 / 500000000) := by
  have h := checkLog_sound (w := (111204353731 / 611204353731)) (n := 12)
    (lo := (367982957 / 1000000000)) (hi := (183991479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361204353731 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(361204353731 / 250000000000) = 1/(250000000000 / 361204353731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (367982957 / 1000000000) (183991479 / 500000000) (Real.log (361204353731 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (361204353731 / 250000000000) = -Real.log (250000000000 / 361204353731) := by
    rw [show ((361204353731 / 250000000000) : ℝ) = ((250000000000 / 361204353731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2103973 / 62500000) ≤ -Real.log (966896744751 / 1000000000000) ∧
    -Real.log (966896744751 / 1000000000000) ≤ (33663569 / 1000000000) := by
  have h := checkLog_sound (w := (33103255249 / 1966896744751)) (n := 12)
    (lo := (2103973 / 62500000)) (hi := (33663569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 966896744751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 966896744751) = 1/(966896744751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-33663569 / 1000000000) (-2103973 / 62500000) (Real.log (966896744751 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (33545129 / 1000000000) ≤ -Real.log (60438204351 / 62500000000) ∧
    -Real.log (60438204351 / 62500000000) ≤ (3354513 / 100000000) := by
  have h := checkLog_sound (w := (2061795649 / 122938204351)) (n := 12)
    (lo := (33545129 / 1000000000)) (hi := (3354513 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60438204351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60438204351) = 1/(60438204351 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-3354513 / 100000000) (-33545129 / 1000000000) (Real.log (60438204351 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell179
