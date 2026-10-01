import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0375
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

theorem reflection_log_1_neg : (25775501 / 125000000) ≤ -Real.log (2048 / 2517) ∧
    -Real.log (2048 / 2517) ≤ (206204009 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 4565)) (n := 12)
    (lo := (25775501 / 125000000)) (hi := (206204009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2517 / 2048) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2517 / 2048) = 1/(2048 / 2517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (25775501 / 125000000) (206204009 / 1000000000) (Real.log (2517 / 2048)) := by
  have h := reflection_log_1_neg
  have he : Real.log (2517 / 2048) = -Real.log (2048 / 2517) := by
    rw [show ((2517 / 2048) : ℝ) = ((2048 / 2517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (260071971 / 1000000000) ≤ -Real.log (1579 / 2048) ∧
    -Real.log (1579 / 2048) ≤ (65017993 / 250000000) := by
  have h := checkLog_sound (w := (469 / 3627)) (n := 12)
    (lo := (260071971 / 1000000000)) (hi := (65017993 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2048 / 1579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2048 / 1579) = 1/(1579 / 2048) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-65017993 / 250000000) (-260071971 / 1000000000) (Real.log (1579 / 2048)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (205965601 / 1000000000) ≤ -Real.log (5120 / 6291) ∧
    -Real.log (5120 / 6291) ≤ (102982801 / 500000000) := by
  have h := checkLog_sound (w := (1171 / 11411)) (n := 12)
    (lo := (205965601 / 1000000000)) (hi := (102982801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6291 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6291 / 5120) = 1/(5120 / 6291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (205965601 / 1000000000) (102982801 / 500000000) (Real.log (6291 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6291 / 5120) = -Real.log (5120 / 6291) := by
    rw [show ((6291 / 5120) : ℝ) = ((5120 / 6291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (32461507 / 125000000) ≤ -Real.log (3949 / 5120) ∧
    -Real.log (3949 / 5120) ≤ (259692057 / 1000000000) := by
  have h := checkLog_sound (w := (1171 / 9069)) (n := 12)
    (lo := (32461507 / 125000000)) (hi := (259692057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3949) = 1/(3949 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-259692057 / 1000000000) (-32461507 / 125000000) (Real.log (3949 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (377070991 / 1000000000) ≤ -Real.log (1024 / 1493) ∧
    -Real.log (1024 / 1493) ≤ (23566937 / 62500000) := by
  have h := checkLog_sound (w := (469 / 2517)) (n := 12)
    (lo := (377070991 / 1000000000)) (hi := (23566937 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1493 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1493 / 1024) = 1/(1024 / 1493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (377070991 / 1000000000) (23566937 / 62500000) (Real.log (1493 / 1024)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1493 / 1024) = -Real.log (1024 / 1493) := by
    rw [show ((1493 / 1024) : ℝ) = ((1024 / 1493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (612503691 / 1000000000) ≤ -Real.log (555 / 1024) ∧
    -Real.log (555 / 1024) ≤ (153125923 / 250000000) := by
  have h := checkLog_sound (w := (469 / 1579)) (n := 12)
    (lo := (612503691 / 1000000000)) (hi := (153125923 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 555) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 555) = 1/(555 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-153125923 / 250000000) (-612503691 / 1000000000) (Real.log (555 / 1024)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (75333807 / 200000000) ≤ -Real.log (2560 / 3731) ∧
    -Real.log (2560 / 3731) ≤ (94167259 / 250000000) := by
  have h := checkLog_sound (w := (1171 / 6291)) (n := 12)
    (lo := (75333807 / 200000000)) (hi := (94167259 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3731 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3731 / 2560) = 1/(2560 / 3731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (75333807 / 200000000) (94167259 / 250000000) (Real.log (3731 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3731 / 2560) = -Real.log (2560 / 3731) := by
    rw [show ((3731 / 2560) : ℝ) = ((2560 / 3731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (305711597 / 500000000) ≤ -Real.log (1389 / 2560) ∧
    -Real.log (1389 / 2560) ≤ (122284639 / 200000000) := by
  have h := checkLog_sound (w := (1171 / 3949)) (n := 12)
    (lo := (305711597 / 500000000)) (hi := (122284639 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1389) = 1/(1389 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-122284639 / 200000000) (-305711597 / 500000000) (Real.log (1389 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (141287401 / 500000000) ≤ -Real.log (1000000 / 1326541) ∧
    -Real.log (1000000 / 1326541) ≤ (282574803 / 1000000000) := by
  have h := checkLog_sound (w := (326541 / 2326541)) (n := 12)
    (lo := (141287401 / 500000000)) (hi := (282574803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1326541 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1326541 / 1000000) = 1/(1000000 / 1326541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (141287401 / 500000000) (282574803 / 1000000000) (Real.log (1326541 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1326541 / 1000000) = -Real.log (1000000 / 1326541) := by
    rw [show ((1326541 / 1000000) : ℝ) = ((1000000 / 1326541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (395328161 / 1000000000) ≤ -Real.log (673459 / 1000000) ∧
    -Real.log (673459 / 1000000) ≤ (197664081 / 500000000) := by
  have h := checkLog_sound (w := (326541 / 1673459)) (n := 12)
    (lo := (395328161 / 1000000000)) (hi := (197664081 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 673459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 673459) = 1/(673459 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-197664081 / 500000000) (-395328161 / 1000000000) (Real.log (673459 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (282898147 / 1000000000) ≤ -Real.log (100000 / 132697) ∧
    -Real.log (100000 / 132697) ≤ (70724537 / 250000000) := by
  have h := checkLog_sound (w := (32697 / 232697)) (n := 12)
    (lo := (282898147 / 1000000000)) (hi := (70724537 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((132697 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(132697 / 100000) = 1/(100000 / 132697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (282898147 / 1000000000) (70724537 / 250000000) (Real.log (132697 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (132697 / 100000) = -Real.log (100000 / 132697) := by
    rw [show ((132697 / 100000) : ℝ) = ((100000 / 132697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (395965373 / 1000000000) ≤ -Real.log (67303 / 100000) ∧
    -Real.log (67303 / 100000) ≤ (197982687 / 500000000) := by
  have h := checkLog_sound (w := (32697 / 167303)) (n := 12)
    (lo := (395965373 / 1000000000)) (hi := (197982687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 67303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 67303) = 1/(67303 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-197982687 / 500000000) (-395965373 / 1000000000) (Real.log (67303 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (213433359 / 1000000000) ≤ -Real.log (1000000 / 1237921) ∧
    -Real.log (1000000 / 1237921) ≤ (2667917 / 12500000) := by
  have h := checkLog_sound (w := (237921 / 2237921)) (n := 12)
    (lo := (213433359 / 1000000000)) (hi := (2667917 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1237921 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1237921 / 1000000) = 1/(1000000 / 1237921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (213433359 / 1000000000) (2667917 / 12500000) (Real.log (1237921 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1237921 / 1000000) = -Real.log (1000000 / 1237921) := by
    rw [show ((1237921 / 1000000) : ℝ) = ((1000000 / 1237921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (135852527 / 500000000) ≤ -Real.log (762079 / 1000000) ∧
    -Real.log (762079 / 1000000) ≤ (54341011 / 200000000) := by
  have h := checkLog_sound (w := (237921 / 1762079)) (n := 12)
    (lo := (135852527 / 500000000)) (hi := (54341011 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 762079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 762079) = 1/(762079 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-54341011 / 200000000) (-135852527 / 500000000) (Real.log (762079 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (42740303 / 200000000) ≤ -Real.log (1000000 / 1238253) ∧
    -Real.log (1000000 / 1238253) ≤ (53425379 / 250000000) := by
  have h := checkLog_sound (w := (238253 / 2238253)) (n := 12)
    (lo := (42740303 / 200000000)) (hi := (53425379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1238253 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1238253 / 1000000) = 1/(1000000 / 1238253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (42740303 / 200000000) (53425379 / 250000000) (Real.log (1238253 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1238253 / 1000000) = -Real.log (1000000 / 1238253) := by
    rw [show ((1238253 / 1000000) : ℝ) = ((1000000 / 1238253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (272140799 / 1000000000) ≤ -Real.log (761747 / 1000000) ∧
    -Real.log (761747 / 1000000) ≤ (21261 / 78125) := by
  have h := checkLog_sound (w := (238253 / 1761747)) (n := 12)
    (lo := (272140799 / 1000000000)) (hi := (21261 / 78125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 761747) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 761747) = 1/(761747 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-21261 / 78125) (-272140799 / 1000000000) (Real.log (761747 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (677902963 / 1000000000) ≤ -Real.log (62500000000 / 123108923483) ∧
    -Real.log (62500000000 / 123108923483) ≤ (169475741 / 250000000) := by
  have h := checkLog_sound (w := (60608923483 / 185608923483)) (n := 12)
    (lo := (677902963 / 1000000000)) (hi := (169475741 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123108923483 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123108923483 / 62500000000) = 1/(62500000000 / 123108923483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (677902963 / 1000000000) (169475741 / 250000000) (Real.log (123108923483 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (123108923483 / 62500000000) = -Real.log (62500000000 / 123108923483) := by
    rw [show ((123108923483 / 62500000000) : ℝ) = ((62500000000 / 123108923483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (678863521 / 1000000000) ≤ -Real.log (250000000000 / 492908934223) ∧
    -Real.log (250000000000 / 492908934223) ≤ (339431761 / 500000000) := by
  have h := checkLog_sound (w := (242908934223 / 742908934223)) (n := 12)
    (lo := (678863521 / 1000000000)) (hi := (339431761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((492908934223 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(492908934223 / 250000000000) = 1/(250000000000 / 492908934223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (678863521 / 1000000000) (339431761 / 500000000) (Real.log (492908934223 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (492908934223 / 250000000000) = -Real.log (250000000000 / 492908934223) := by
    rw [show ((492908934223 / 250000000000) : ℝ) = ((250000000000 / 492908934223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (485138413 / 1000000000) ≤ -Real.log (500000000000 / 812199916281) ∧
    -Real.log (500000000000 / 812199916281) ≤ (242569207 / 500000000) := by
  have h := checkLog_sound (w := (312199916281 / 1312199916281)) (n := 12)
    (lo := (485138413 / 1000000000)) (hi := (242569207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((812199916281 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(812199916281 / 500000000000) = 1/(500000000000 / 812199916281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (485138413 / 1000000000) (242569207 / 500000000) (Real.log (812199916281 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (812199916281 / 500000000000) = -Real.log (500000000000 / 812199916281) := by
    rw [show ((812199916281 / 500000000000) : ℝ) = ((500000000000 / 812199916281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (242921157 / 500000000) ≤ -Real.log (500000000000 / 812771825817) ∧
    -Real.log (500000000000 / 812771825817) ≤ (97168463 / 200000000) := by
  have h := checkLog_sound (w := (312771825817 / 1312771825817)) (n := 12)
    (lo := (242921157 / 500000000)) (hi := (97168463 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((812771825817 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(812771825817 / 500000000000) = 1/(500000000000 / 812771825817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (242921157 / 500000000) (97168463 / 200000000) (Real.log (812771825817 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (812771825817 / 500000000000) = -Real.log (500000000000 / 812771825817) := by
    rw [show ((812771825817 / 500000000000) : ℝ) = ((500000000000 / 812771825817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0375
