import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell220
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

theorem reflection_log_1_neg : (321715451 / 1000000000) ≤ -Real.log (5120 / 7063) ∧
    -Real.log (5120 / 7063) ≤ (80428863 / 250000000) := by
  have h := checkLog_sound (w := (1943 / 12183)) (n := 12)
    (lo := (321715451 / 1000000000)) (hi := (80428863 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7063 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7063 / 5120) = 1/(5120 / 7063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (321715451 / 1000000000) (80428863 / 250000000) (Real.log (7063 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (7063 / 5120) = -Real.log (5120 / 7063) := by
    rw [show ((7063 / 5120) : ℝ) = ((5120 / 7063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (477217083 / 1000000000) ≤ -Real.log (3177 / 5120) ∧
    -Real.log (3177 / 5120) ≤ (119304271 / 250000000) := by
  have h := checkLog_sound (w := (1943 / 8297)) (n := 12)
    (lo := (477217083 / 1000000000)) (hi := (119304271 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3177) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3177) = 1/(3177 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-119304271 / 250000000) (-477217083 / 1000000000) (Real.log (3177 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (80322653 / 250000000) ≤ -Real.log (256 / 353) ∧
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


theorem reflection_log_3 : Bounds (80322653 / 250000000) (321290613 / 1000000000) (Real.log (353 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (353 / 256) = -Real.log (256 / 353) := by
    rw [show ((353 / 256) : ℝ) = ((256 / 353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (238136621 / 500000000) ≤ -Real.log (159 / 256) ∧
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


theorem reflection_log_4 : Bounds (-476273243 / 1000000000) (-238136621 / 500000000) (Real.log (159 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (119363941 / 500000000) ≤ -Real.log (1000000 / 1269633) ∧
    -Real.log (1000000 / 1269633) ≤ (238727883 / 1000000000) := by
  have h := checkLog_sound (w := (269633 / 2269633)) (n := 12)
    (lo := (119363941 / 500000000)) (hi := (238727883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1269633 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1269633 / 1000000) = 1/(1000000 / 1269633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (119363941 / 500000000) (238727883 / 1000000000) (Real.log (1269633 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1269633 / 1000000) = -Real.log (1000000 / 1269633) := by
    rw [show ((1269633 / 1000000) : ℝ) = ((1000000 / 1269633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (314208131 / 1000000000) ≤ -Real.log (730367 / 1000000) ∧
    -Real.log (730367 / 1000000) ≤ (78552033 / 250000000) := by
  have h := checkLog_sound (w := (269633 / 1730367)) (n := 12)
    (lo := (314208131 / 1000000000)) (hi := (78552033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 730367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 730367) = 1/(730367 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-78552033 / 250000000) (-314208131 / 1000000000) (Real.log (730367 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (239060993 / 1000000000) ≤ -Real.log (125000 / 158757) ∧
    -Real.log (125000 / 158757) ≤ (119530497 / 500000000) := by
  have h := checkLog_sound (w := (33757 / 283757)) (n := 12)
    (lo := (239060993 / 1000000000)) (hi := (119530497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158757 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(158757 / 125000) = 1/(125000 / 158757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (239060993 / 1000000000) (119530497 / 500000000) (Real.log (158757 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (158757 / 125000) = -Real.log (125000 / 158757) := by
    rw [show ((158757 / 125000) : ℝ) = ((125000 / 158757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (15739373 / 50000000) ≤ -Real.log (91243 / 125000) ∧
    -Real.log (91243 / 125000) ≤ (314787461 / 1000000000) := by
  have h := checkLog_sound (w := (33757 / 216243)) (n := 12)
    (lo := (15739373 / 50000000)) (hi := (314787461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 91243) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 91243) = 1/(91243 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-314787461 / 1000000000) (-15739373 / 50000000) (Real.log (91243 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (177792147 / 1000000000) ≤ -Real.log (1000000 / 1194577) ∧
    -Real.log (1000000 / 1194577) ≤ (44448037 / 250000000) := by
  have h := checkLog_sound (w := (194577 / 2194577)) (n := 12)
    (lo := (177792147 / 1000000000)) (hi := (44448037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1194577 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1194577 / 1000000) = 1/(1000000 / 1194577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (177792147 / 1000000000) (44448037 / 250000000) (Real.log (1194577 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1194577 / 1000000) = -Real.log (1000000 / 1194577) := by
    rw [show ((1194577 / 1000000) : ℝ) = ((1000000 / 1194577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (216387673 / 1000000000) ≤ -Real.log (805423 / 1000000) ∧
    -Real.log (805423 / 1000000) ≤ (108193837 / 500000000) := by
  have h := checkLog_sound (w := (194577 / 1805423)) (n := 12)
    (lo := (216387673 / 1000000000)) (hi := (108193837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 805423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 805423) = 1/(805423 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-108193837 / 500000000) (-216387673 / 1000000000) (Real.log (805423 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (11128697 / 62500000) ≤ -Real.log (62500 / 74681) ∧
    -Real.log (62500 / 74681) ≤ (178059153 / 1000000000) := by
  have h := checkLog_sound (w := (12181 / 137181)) (n := 12)
    (lo := (11128697 / 62500000)) (hi := (178059153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74681 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74681 / 62500) = 1/(62500 / 74681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (11128697 / 62500000) (178059153 / 1000000000) (Real.log (74681 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (74681 / 62500) = -Real.log (62500 / 74681) := by
    rw [show ((74681 / 62500) : ℝ) = ((62500 / 74681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (216783817 / 1000000000) ≤ -Real.log (50319 / 62500) ∧
    -Real.log (50319 / 62500) ≤ (108391909 / 500000000) := by
  have h := checkLog_sound (w := (12181 / 112819)) (n := 12)
    (lo := (216783817 / 1000000000)) (hi := (108391909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 50319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 50319) = 1/(50319 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-108391909 / 500000000) (-216783817 / 1000000000) (Real.log (50319 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (398781927 / 500000000) ≤ -Real.log (500000000000 / 1110062893081) ∧
    -Real.log (500000000000 / 1110062893081) ≤ (49847741 / 62500000) := by
  have h := checkLog_sound (w := (110062893081 / 2110062893081)) (n := 12)
    (lo := (52208337 / 500000000)) (hi := (4176667 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1110062893081 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1110062893081 / 1000000000000) = 1/(500000000000 / 1110062893081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (398781927 / 500000000) (49847741 / 62500000) (Real.log (1110062893081 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1110062893081 / 500000000000) = -Real.log (500000000000 / 1110062893081) := by
    rw [show ((1110062893081 / 500000000000) : ℝ) = ((500000000000 / 1110062893081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (399466267 / 500000000) ≤ -Real.log (500000000000 / 1111583254643) ∧
    -Real.log (500000000000 / 1111583254643) ≤ (99866567 / 125000000) := by
  have h := checkLog_sound (w := (111583254643 / 2111583254643)) (n := 12)
    (lo := (52892677 / 500000000)) (hi := (21157071 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1111583254643 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1111583254643 / 1000000000000) = 1/(500000000000 / 1111583254643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (399466267 / 500000000) (99866567 / 125000000) (Real.log (1111583254643 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1111583254643 / 500000000000) = -Real.log (500000000000 / 1111583254643) := by
    rw [show ((1111583254643 / 500000000000) : ℝ) = ((500000000000 / 1111583254643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (552936013 / 1000000000) ≤ -Real.log (500000000000 / 869174675197) ∧
    -Real.log (500000000000 / 869174675197) ≤ (276468007 / 500000000) := by
  have h := checkLog_sound (w := (369174675197 / 1369174675197)) (n := 12)
    (lo := (552936013 / 1000000000)) (hi := (276468007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((869174675197 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(869174675197 / 500000000000) = 1/(500000000000 / 869174675197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (552936013 / 1000000000) (276468007 / 500000000) (Real.log (869174675197 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (869174675197 / 500000000000) = -Real.log (500000000000 / 869174675197) := by
    rw [show ((869174675197 / 500000000000) : ℝ) = ((500000000000 / 869174675197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (276924227 / 500000000) ≤ -Real.log (500000000000 / 869968107143) ∧
    -Real.log (500000000000 / 869968107143) ≤ (110769691 / 200000000) := by
  have h := checkLog_sound (w := (369968107143 / 1369968107143)) (n := 12)
    (lo := (276924227 / 500000000)) (hi := (110769691 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((869968107143 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(869968107143 / 500000000000) = 1/(500000000000 / 869968107143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (276924227 / 500000000) (110769691 / 200000000) (Real.log (869968107143 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (869968107143 / 500000000000) = -Real.log (500000000000 / 869968107143) := by
    rw [show ((869968107143 / 500000000000) : ℝ) = ((500000000000 / 869968107143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (394179821 / 1000000000) ≤ -Real.log (500000000000 / 741583615069) ∧
    -Real.log (500000000000 / 741583615069) ≤ (197089911 / 500000000) := by
  have h := checkLog_sound (w := (241583615069 / 1241583615069)) (n := 12)
    (lo := (394179821 / 1000000000)) (hi := (197089911 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((741583615069 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(741583615069 / 500000000000) = 1/(500000000000 / 741583615069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (394179821 / 1000000000) (197089911 / 500000000) (Real.log (741583615069 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (741583615069 / 500000000000) = -Real.log (500000000000 / 741583615069) := by
    rw [show ((741583615069 / 500000000000) : ℝ) = ((500000000000 / 741583615069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (394842969 / 1000000000) ≤ -Real.log (500000000000 / 742075557941) ∧
    -Real.log (500000000000 / 742075557941) ≤ (39484297 / 100000000) := by
  have h := checkLog_sound (w := (242075557941 / 1242075557941)) (n := 12)
    (lo := (394842969 / 1000000000)) (hi := (39484297 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((742075557941 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(742075557941 / 500000000000) = 1/(500000000000 / 742075557941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (394842969 / 1000000000) (39484297 / 100000000) (Real.log (742075557941 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (742075557941 / 500000000000) = -Real.log (500000000000 / 742075557941) := by
    rw [show ((742075557941 / 500000000000) : ℝ) = ((500000000000 / 742075557941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (7744933 / 200000000) ≤ -Real.log (3757873239 / 3906250000) ∧
    -Real.log (3757873239 / 3906250000) ≤ (19362333 / 500000000) := by
  have h := checkLog_sound (w := (148376761 / 7664123239)) (n := 12)
    (lo := (7744933 / 200000000)) (hi := (19362333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3757873239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3757873239) = 1/(3757873239 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-19362333 / 500000000) (-7744933 / 200000000) (Real.log (3757873239 / 3906250000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1543821 / 40000000) ≤ -Real.log (962139791071 / 1000000000000) ∧
    -Real.log (962139791071 / 1000000000000) ≤ (19297763 / 500000000) := by
  have h := checkLog_sound (w := (37860208929 / 1962139791071)) (n := 12)
    (lo := (1543821 / 40000000)) (hi := (19297763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 962139791071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 962139791071) = 1/(962139791071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-19297763 / 500000000) (-1543821 / 40000000) (Real.log (962139791071 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell220
