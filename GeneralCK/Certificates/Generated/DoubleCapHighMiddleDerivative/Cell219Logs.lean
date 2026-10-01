import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell219
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

theorem reflection_log_1_neg : (80322653 / 250000000) ≤ -Real.log (256 / 353) ∧
    -Real.log (256 / 353) ≤ (321290613 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 609)) (n := 12)
    (lo := (80322653 / 250000000)) (hi := (321290613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(353 / 256) = 1/(256 / 353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (80322653 / 250000000) (321290613 / 1000000000) (Real.log (353 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (353 / 256) = -Real.log (256 / 353) := by
    rw [show ((353 / 256) : ℝ) = ((256 / 353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (238136621 / 500000000) ≤ -Real.log (159 / 256) ∧
    -Real.log (159 / 256) ≤ (476273243 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 415)) (n := 12)
    (lo := (238136621 / 500000000)) (hi := (476273243 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 159) = 1/(159 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-476273243 / 1000000000) (-238136621 / 500000000) (Real.log (159 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (40108199 / 125000000) ≤ -Real.log (5120 / 7057) ∧
    -Real.log (5120 / 7057) ≤ (320865593 / 1000000000) := by
  have h := checkLog_sound (w := (1937 / 12177)) (n := 12)
    (lo := (40108199 / 125000000)) (hi := (320865593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7057 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7057 / 5120) = 1/(5120 / 7057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (40108199 / 125000000) (320865593 / 1000000000) (Real.log (7057 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (7057 / 5120) = -Real.log (5120 / 7057) := by
    rw [show ((7057 / 5120) : ℝ) = ((5120 / 7057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (47533029 / 100000000) ≤ -Real.log (3183 / 5120) ∧
    -Real.log (3183 / 5120) ≤ (475330291 / 1000000000) := by
  have h := checkLog_sound (w := (1937 / 8303)) (n := 12)
    (lo := (47533029 / 100000000)) (hi := (475330291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3183) = 1/(3183 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-475330291 / 1000000000) (-47533029 / 100000000) (Real.log (3183 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (238394659 / 1000000000) ≤ -Real.log (100000 / 126921) ∧
    -Real.log (100000 / 126921) ≤ (11919733 / 50000000) := by
  have h := checkLog_sound (w := (26921 / 226921)) (n := 12)
    (lo := (238394659 / 1000000000)) (hi := (11919733 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126921 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(126921 / 100000) = 1/(100000 / 126921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (238394659 / 1000000000) (11919733 / 50000000) (Real.log (126921 / 100000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (126921 / 100000) = -Real.log (100000 / 126921) := by
    rw [show ((126921 / 100000) : ℝ) = ((100000 / 126921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (156814569 / 500000000) ≤ -Real.log (73079 / 100000) ∧
    -Real.log (73079 / 100000) ≤ (313629139 / 1000000000) := by
  have h := checkLog_sound (w := (26921 / 173079)) (n := 12)
    (lo := (156814569 / 500000000)) (hi := (313629139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 73079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 73079) = 1/(73079 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-313629139 / 1000000000) (-156814569 / 500000000) (Real.log (73079 / 100000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (238728669 / 1000000000) ≤ -Real.log (500000 / 634817) ∧
    -Real.log (500000 / 634817) ≤ (23872867 / 100000000) := by
  have h := checkLog_sound (w := (134817 / 1134817)) (n := 12)
    (lo := (238728669 / 1000000000)) (hi := (23872867 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((634817 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(634817 / 500000) = 1/(500000 / 634817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (238728669 / 1000000000) (23872867 / 100000000) (Real.log (634817 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (634817 / 500000) = -Real.log (500000 / 634817) := by
    rw [show ((634817 / 500000) : ℝ) = ((500000 / 634817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (628419 / 2000000) ≤ -Real.log (365183 / 500000) ∧
    -Real.log (365183 / 500000) ≤ (314209501 / 1000000000) := by
  have h := checkLog_sound (w := (134817 / 865183)) (n := 12)
    (lo := (628419 / 2000000)) (hi := (314209501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 365183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 365183) = 1/(365183 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-314209501 / 1000000000) (-628419 / 2000000) (Real.log (365183 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (88763373 / 500000000) ≤ -Real.log (50000 / 59713) ∧
    -Real.log (50000 / 59713) ≤ (177526747 / 1000000000) := by
  have h := checkLog_sound (w := (9713 / 109713)) (n := 12)
    (lo := (88763373 / 500000000)) (hi := (177526747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59713 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59713 / 50000) = 1/(50000 / 59713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (88763373 / 500000000) (177526747 / 1000000000) (Real.log (59713 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (59713 / 50000) = -Real.log (50000 / 59713) := by
    rw [show ((59713 / 50000) : ℝ) = ((50000 / 59713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (215994169 / 1000000000) ≤ -Real.log (40287 / 50000) ∧
    -Real.log (40287 / 50000) ≤ (21599417 / 100000000) := by
  have h := checkLog_sound (w := (9713 / 90287)) (n := 12)
    (lo := (215994169 / 1000000000)) (hi := (21599417 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 40287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 40287) = 1/(40287 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-21599417 / 100000000) (-215994169 / 1000000000) (Real.log (40287 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (22224123 / 125000000) ≤ -Real.log (500000 / 597289) ∧
    -Real.log (500000 / 597289) ≤ (35558597 / 200000000) := by
  have h := checkLog_sound (w := (97289 / 1097289)) (n := 12)
    (lo := (22224123 / 125000000)) (hi := (35558597 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597289 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597289 / 500000) = 1/(500000 / 597289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (22224123 / 125000000) (35558597 / 200000000) (Real.log (597289 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (597289 / 500000) = -Real.log (500000 / 597289) := by
    rw [show ((597289 / 500000) : ℝ) = ((500000 / 597289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (43277783 / 200000000) ≤ -Real.log (402711 / 500000) ∧
    -Real.log (402711 / 500000) ≤ (54097229 / 250000000) := by
  have h := checkLog_sound (w := (97289 / 902711)) (n := 12)
    (lo := (43277783 / 200000000)) (hi := (54097229 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 402711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 402711) = 1/(402711 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-54097229 / 250000000) (-43277783 / 200000000) (Real.log (402711 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (796195883 / 1000000000) ≤ -Real.log (500000000000 / 1108545397423) ∧
    -Real.log (500000000000 / 1108545397423) ≤ (159239177 / 200000000) := by
  have h := checkLog_sound (w := (108545397423 / 2108545397423)) (n := 12)
    (lo := (103048703 / 1000000000)) (hi := (201267 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1108545397423 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1108545397423 / 1000000000000) = 1/(500000000000 / 1108545397423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (796195883 / 1000000000) (159239177 / 200000000) (Real.log (1108545397423 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1108545397423 / 500000000000) = -Real.log (500000000000 / 1108545397423) := by
    rw [show ((1108545397423 / 500000000000) : ℝ) = ((500000000000 / 1108545397423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (398781927 / 500000000) ≤ -Real.log (250000000000 / 555031446541) ∧
    -Real.log (250000000000 / 555031446541) ≤ (49847741 / 62500000) := by
  have h := checkLog_sound (w := (55031446541 / 1055031446541)) (n := 12)
    (lo := (52208337 / 500000000)) (hi := (4176667 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((555031446541 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(555031446541 / 500000000000) = 1/(250000000000 / 555031446541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (398781927 / 500000000) (49847741 / 62500000) (Real.log (555031446541 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (555031446541 / 250000000000) = -Real.log (250000000000 / 555031446541) := by
    rw [show ((555031446541 / 250000000000) : ℝ) = ((250000000000 / 555031446541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (552023797 / 1000000000) ≤ -Real.log (50000000000 / 86838216177) ∧
    -Real.log (50000000000 / 86838216177) ≤ (276011899 / 500000000) := by
  have h := checkLog_sound (w := (36838216177 / 136838216177)) (n := 12)
    (lo := (552023797 / 1000000000)) (hi := (276011899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86838216177 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86838216177 / 50000000000) = 1/(50000000000 / 86838216177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (552023797 / 1000000000) (276011899 / 500000000) (Real.log (86838216177 / 50000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (86838216177 / 50000000000) = -Real.log (50000000000 / 86838216177) := by
    rw [show ((86838216177 / 50000000000) : ℝ) = ((50000000000 / 86838216177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (55293817 / 100000000) ≤ -Real.log (6250000000 / 10864706873) ∧
    -Real.log (6250000000 / 10864706873) ≤ (552938171 / 1000000000) := by
  have h := checkLog_sound (w := (4614706873 / 17114706873)) (n := 12)
    (lo := (55293817 / 100000000)) (hi := (552938171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10864706873 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10864706873 / 6250000000) = 1/(6250000000 / 10864706873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (55293817 / 100000000) (552938171 / 1000000000) (Real.log (10864706873 / 6250000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (10864706873 / 6250000000) = -Real.log (6250000000 / 10864706873) := by
    rw [show ((10864706873 / 6250000000) : ℝ) = ((6250000000 / 10864706873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (78704183 / 200000000) ≤ -Real.log (500000000000 / 741095142353) ∧
    -Real.log (500000000000 / 741095142353) ≤ (98380229 / 250000000) := by
  have h := checkLog_sound (w := (241095142353 / 1241095142353)) (n := 12)
    (lo := (78704183 / 200000000)) (hi := (98380229 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741095142353 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741095142353 / 500000000000) = 1/(500000000000 / 741095142353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (78704183 / 200000000) (98380229 / 250000000) (Real.log (741095142353 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (741095142353 / 500000000000) = -Real.log (500000000000 / 741095142353) := by
    rw [show ((741095142353 / 500000000000) : ℝ) = ((500000000000 / 741095142353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3941819 / 10000000) ≤ -Real.log (250000000000 / 370792578301) ∧
    -Real.log (250000000000 / 370792578301) ≤ (394181901 / 1000000000) := by
  have h := checkLog_sound (w := (120792578301 / 620792578301)) (n := 12)
    (lo := (3941819 / 10000000)) (hi := (394181901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((370792578301 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(370792578301 / 250000000000) = 1/(250000000000 / 370792578301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3941819 / 10000000) (394181901 / 1000000000) (Real.log (370792578301 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (370792578301 / 250000000000) = -Real.log (250000000000 / 370792578301) := by
    rw [show ((370792578301 / 250000000000) : ℝ) = ((250000000000 / 370792578301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3859593 / 100000000) ≤ -Real.log (240534850479 / 250000000000) ∧
    -Real.log (240534850479 / 250000000000) ≤ (38595931 / 1000000000) := by
  have h := checkLog_sound (w := (9465149521 / 490534850479)) (n := 12)
    (lo := (3859593 / 100000000)) (hi := (38595931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240534850479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240534850479) = 1/(240534850479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-38595931 / 1000000000) (-3859593 / 100000000) (Real.log (240534850479 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (19233711 / 500000000) ≤ -Real.log (2405657631 / 2500000000) ∧
    -Real.log (2405657631 / 2500000000) ≤ (38467423 / 1000000000) := by
  have h := checkLog_sound (w := (94342369 / 4905657631)) (n := 12)
    (lo := (19233711 / 500000000)) (hi := (38467423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2405657631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2405657631) = 1/(2405657631 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-38467423 / 1000000000) (-19233711 / 500000000) (Real.log (2405657631 / 2500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell219
