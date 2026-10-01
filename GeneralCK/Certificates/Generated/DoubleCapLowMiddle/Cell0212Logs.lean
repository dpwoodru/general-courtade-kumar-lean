import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0212
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

theorem reflection_log_1_neg : (2155889 / 3906250) ≤ -Real.log (3200 / 5557) ∧
    -Real.log (3200 / 5557) ≤ (110381517 / 200000000) := by
  have h := checkLog_sound (w := (2357 / 8757)) (n := 12)
    (lo := (2155889 / 3906250)) (hi := (110381517 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5557 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5557 / 3200) = 1/(3200 / 5557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (2155889 / 3906250) (110381517 / 200000000) (Real.log (5557 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (5557 / 3200) = -Real.log (3200 / 5557) := by
    rw [show ((5557 / 3200) : ℝ) = ((3200 / 5557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (133393913 / 100000000) ≤ -Real.log (843 / 3200) ∧
    -Real.log (843 / 3200) ≤ (333484783 / 250000000) := by
  have h := checkLog_sound (w := (757 / 2443)) (n := 12)
    (lo := (12815839 / 20000000)) (hi := (640791951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 843) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1600 / 843) = 1/(843 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-333484783 / 250000000) (-133393913 / 100000000) (Real.log (843 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (274241307 / 500000000) ≤ -Real.log (1600 / 2769) ∧
    -Real.log (1600 / 2769) ≤ (109696523 / 200000000) := by
  have h := checkLog_sound (w := (1169 / 4369)) (n := 12)
    (lo := (274241307 / 500000000)) (hi := (109696523 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2769 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2769 / 1600) = 1/(1600 / 2769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (274241307 / 500000000) (109696523 / 200000000) (Real.log (2769 / 1600)) := by
  have h := reflection_log_3_neg
  have he : Real.log (2769 / 1600) = -Real.log (1600 / 2769) := by
    rw [show ((2769 / 1600) : ℝ) = ((1600 / 2769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1311650817 / 1000000000) ≤ -Real.log (431 / 1600) ∧
    -Real.log (431 / 1600) ≤ (1311650819 / 1000000000) := by
  have h := checkLog_sound (w := (369 / 1231)) (n := 12)
    (lo := (618503637 / 1000000000)) (hi := (309251819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 431) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 431) = 1/(431 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1311650819 / 1000000000) (-1311650817 / 1000000000) (Real.log (431 / 1600)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (193692997 / 500000000) ≤ -Real.log (1600 / 2357) ∧
    -Real.log (1600 / 2357) ≤ (77477199 / 200000000) := by
  have h := checkLog_sound (w := (757 / 3957)) (n := 12)
    (lo := (193692997 / 500000000)) (hi := (77477199 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2357 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2357 / 1600) = 1/(1600 / 2357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (193692997 / 500000000) (77477199 / 200000000) (Real.log (2357 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2357 / 1600) = -Real.log (1600 / 2357) := by
    rw [show ((2357 / 1600) : ℝ) = ((1600 / 2357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (12815839 / 20000000) ≤ -Real.log (843 / 1600) ∧
    -Real.log (843 / 1600) ≤ (640791951 / 1000000000) := by
  have h := checkLog_sound (w := (757 / 2443)) (n := 12)
    (lo := (12815839 / 20000000)) (hi := (640791951 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600 / 843) = 1/(843 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-640791951 / 1000000000) (-12815839 / 20000000) (Real.log (843 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (379292233 / 1000000000) ≤ -Real.log (800 / 1169) ∧
    -Real.log (800 / 1169) ≤ (189646117 / 500000000) := by
  have h := checkLog_sound (w := (369 / 1969)) (n := 12)
    (lo := (379292233 / 1000000000)) (hi := (189646117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1169 / 800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1169 / 800) = 1/(800 / 1169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (379292233 / 1000000000) (189646117 / 500000000) (Real.log (1169 / 800)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1169 / 800) = -Real.log (800 / 1169) := by
    rw [show ((1169 / 800) : ℝ) = ((800 / 1169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (618503637 / 1000000000) ≤ -Real.log (431 / 800) ∧
    -Real.log (431 / 800) ≤ (309251819 / 500000000) := by
  have h := checkLog_sound (w := (369 / 1231)) (n := 12)
    (lo := (618503637 / 1000000000)) (hi := (309251819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(800 / 431) = 1/(431 / 800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-309251819 / 500000000) (-618503637 / 1000000000) (Real.log (431 / 800)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (604083699 / 1000000000) ≤ -Real.log (40000 / 73183) ∧
    -Real.log (40000 / 73183) ≤ (6040837 / 10000000) := by
  have h := checkLog_sound (w := (33183 / 113183)) (n := 12)
    (lo := (604083699 / 1000000000)) (hi := (6040837 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73183 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73183 / 40000) = 1/(40000 / 73183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (604083699 / 1000000000) (6040837 / 10000000) (Real.log (73183 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (73183 / 40000) = -Real.log (40000 / 73183) := by
    rw [show ((73183 / 40000) : ℝ) = ((40000 / 73183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (44236499 / 25000000) ≤ -Real.log (6817 / 40000) ∧
    -Real.log (6817 / 40000) ≤ (1769459963 / 1000000000) := by
  have h := checkLog_sound (w := (3183 / 16817)) (n := 12)
    (lo := (478957 / 1250000)) (hi := (383165601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 6817) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(10000 / 6817) = 1/(6817 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1769459963 / 1000000000) (-44236499 / 25000000) (Real.log (6817 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (605463941 / 1000000000) ≤ -Real.log (500000 / 916051) ∧
    -Real.log (500000 / 916051) ≤ (302731971 / 500000000) := by
  have h := checkLog_sound (w := (416051 / 1416051)) (n := 12)
    (lo := (605463941 / 1000000000)) (hi := (302731971 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((916051 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(916051 / 500000) = 1/(500000 / 916051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (605463941 / 1000000000) (302731971 / 500000000) (Real.log (916051 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (916051 / 500000) = -Real.log (500000 / 916051) := by
    rw [show ((916051 / 500000) : ℝ) = ((500000 / 916051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (14275189 / 8000000) ≤ -Real.log (83949 / 500000) ∧
    -Real.log (83949 / 500000) ≤ (446099657 / 250000000) := by
  have h := checkLog_sound (w := (41051 / 208949)) (n := 12)
    (lo := (79620853 / 200000000)) (hi := (199052133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 83949) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 83949) = 1/(83949 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-446099657 / 250000000) (-14275189 / 8000000) (Real.log (83949 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (921937 / 1562500) ≤ -Real.log (50000 / 90203) ∧
    -Real.log (50000 / 90203) ≤ (590039681 / 1000000000) := by
  have h := checkLog_sound (w := (40203 / 140203)) (n := 12)
    (lo := (921937 / 1562500)) (hi := (590039681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90203 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90203 / 50000) = 1/(50000 / 90203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (921937 / 1562500) (590039681 / 1000000000) (Real.log (90203 / 50000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (90203 / 50000) = -Real.log (50000 / 90203) := by
    rw [show ((90203 / 50000) : ℝ) = ((50000 / 90203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1629946787 / 1000000000) ≤ -Real.log (9797 / 50000) ∧
    -Real.log (9797 / 50000) ≤ (162994679 / 100000000) := by
  have h := checkLog_sound (w := (2703 / 22297)) (n := 12)
    (lo := (243652427 / 1000000000)) (hi := (60913107 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12500 / 9797) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(12500 / 9797) = 1/(9797 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-162994679 / 100000000) (-1629946787 / 1000000000) (Real.log (9797 / 50000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (148049093 / 250000000) ≤ -Real.log (200000 / 361591) ∧
    -Real.log (200000 / 361591) ≤ (592196373 / 1000000000) := by
  have h := checkLog_sound (w := (161591 / 561591)) (n := 12)
    (lo := (148049093 / 250000000)) (hi := (592196373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361591 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(361591 / 200000) = 1/(200000 / 361591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (148049093 / 250000000) (592196373 / 1000000000) (Real.log (361591 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (361591 / 200000) = -Real.log (200000 / 361591) := by
    rw [show ((361591 / 200000) : ℝ) = ((200000 / 361591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (825012779 / 500000000) ≤ -Real.log (38409 / 200000) ∧
    -Real.log (38409 / 200000) ≤ (1650025561 / 1000000000) := by
  have h := checkLog_sound (w := (11591 / 88409)) (n := 12)
    (lo := (131865599 / 500000000)) (hi := (263731199 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 38409) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 38409) = 1/(38409 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1650025561 / 1000000000) (-825012779 / 500000000) (Real.log (38409 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2373543659 / 1000000000) ≤ -Real.log (250000000000 / 2683841865923) ∧
    -Real.log (250000000000 / 2683841865923) ≤ (2373543663 / 1000000000) := by
  have h := checkLog_sound (w := (683841865923 / 4683841865923)) (n := 12)
    (lo := (294102119 / 1000000000)) (hi := (7352553 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2683841865923 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2683841865923 / 2000000000000) = 1/(250000000000 / 2683841865923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2373543659 / 1000000000) (2373543663 / 1000000000) (Real.log (2683841865923 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2683841865923 / 250000000000) = -Real.log (250000000000 / 2683841865923) := by
    rw [show ((2683841865923 / 250000000000) : ℝ) = ((250000000000 / 2683841865923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1194931283 / 500000000) ≤ -Real.log (250000000000 / 2727998546737) ∧
    -Real.log (250000000000 / 2727998546737) ≤ (238986257 / 100000000) := by
  have h := checkLog_sound (w := (727998546737 / 4727998546737)) (n := 12)
    (lo := (155210513 / 500000000)) (hi := (310421027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2727998546737 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2727998546737 / 2000000000000) = 1/(250000000000 / 2727998546737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1194931283 / 500000000) (238986257 / 100000000) (Real.log (2727998546737 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2727998546737 / 250000000000) = -Real.log (250000000000 / 2727998546737) := by
    rw [show ((2727998546737 / 250000000000) : ℝ) = ((250000000000 / 2727998546737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2219986467 / 1000000000) ≤ -Real.log (500000000000 / 4603603143819) ∧
    -Real.log (500000000000 / 4603603143819) ≤ (2219986471 / 1000000000) := by
  have h := checkLog_sound (w := (603603143819 / 8603603143819)) (n := 12)
    (lo := (140544927 / 1000000000)) (hi := (4392029 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4603603143819 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4603603143819 / 4000000000000) = 1/(500000000000 / 4603603143819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2219986467 / 1000000000) (2219986471 / 1000000000) (Real.log (4603603143819 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (4603603143819 / 500000000000) = -Real.log (500000000000 / 4603603143819) := by
    rw [show ((4603603143819 / 500000000000) : ℝ) = ((500000000000 / 4603603143819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (224222193 / 100000000) ≤ -Real.log (125000000000 / 1176778229061) ∧
    -Real.log (125000000000 / 1176778229061) ≤ (1121110967 / 500000000) := by
  have h := checkLog_sound (w := (176778229061 / 2176778229061)) (n := 12)
    (lo := (16278039 / 100000000)) (hi := (162780391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1176778229061 / 1000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1176778229061 / 1000000000000) = 1/(125000000000 / 1176778229061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (224222193 / 100000000) (1121110967 / 500000000) (Real.log (1176778229061 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1176778229061 / 125000000000) = -Real.log (125000000000 / 1176778229061) := by
    rw [show ((1176778229061 / 125000000000) : ℝ) = ((125000000000 / 1176778229061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0212
