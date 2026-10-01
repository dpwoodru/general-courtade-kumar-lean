import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0171
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

theorem reflection_log_1_neg : (139303911 / 500000000) ≤ -Real.log (1024 / 1353) ∧
    -Real.log (1024 / 1353) ≤ (278607823 / 1000000000) := by
  have h := checkLog_sound (w := (329 / 2377)) (n := 12)
    (lo := (139303911 / 500000000)) (hi := (278607823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1353 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1353 / 1024) = 1/(1024 / 1353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (139303911 / 500000000) (278607823 / 1000000000) (Real.log (1353 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1353 / 1024) = -Real.log (1024 / 1353) := by
    rw [show ((1353 / 1024) : ℝ) = ((1024 / 1353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (9688999 / 25000000) ≤ -Real.log (695 / 1024) ∧
    -Real.log (695 / 1024) ≤ (387559961 / 1000000000) := by
  have h := checkLog_sound (w := (329 / 1719)) (n := 12)
    (lo := (9688999 / 25000000)) (hi := (387559961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 695) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 695) = 1/(695 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-387559961 / 1000000000) (-9688999 / 25000000) (Real.log (695 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (55632853 / 200000000) ≤ -Real.log (2560 / 3381) ∧
    -Real.log (2560 / 3381) ≤ (139082133 / 500000000) := by
  have h := checkLog_sound (w := (821 / 5941)) (n := 12)
    (lo := (55632853 / 200000000)) (hi := (139082133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3381 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3381 / 2560) = 1/(2560 / 3381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (55632853 / 200000000) (139082133 / 500000000) (Real.log (3381 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3381 / 2560) = -Real.log (2560 / 3381) := by
    rw [show ((3381 / 2560) : ℝ) = ((2560 / 3381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (386697023 / 1000000000) ≤ -Real.log (1739 / 2560) ∧
    -Real.log (1739 / 2560) ≤ (6042141 / 15625000) := by
  have h := checkLog_sound (w := (821 / 4299)) (n := 12)
    (lo := (386697023 / 1000000000)) (hi := (6042141 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1739) = 1/(1739 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-6042141 / 15625000) (-386697023 / 1000000000) (Real.log (1739 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (248133517 / 500000000) ≤ -Real.log (512 / 841) ∧
    -Real.log (512 / 841) ≤ (99253407 / 200000000) := by
  have h := checkLog_sound (w := (329 / 1353)) (n := 12)
    (lo := (248133517 / 500000000)) (hi := (99253407 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((841 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(841 / 512) = 1/(512 / 841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (248133517 / 500000000) (99253407 / 200000000) (Real.log (841 / 512)) := by
  have h := reflection_log_5_neg
  have he : Real.log (841 / 512) = -Real.log (512 / 841) := by
    rw [show ((841 / 512) : ℝ) = ((512 / 841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1028838471 / 1000000000) ≤ -Real.log (183 / 512) ∧
    -Real.log (183 / 512) ≤ (1028838473 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 439)) (n := 12)
    (lo := (335691291 / 1000000000)) (hi := (83922823 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 183) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256 / 183) = 1/(183 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1028838473 / 1000000000) (-1028838471 / 1000000000) (Real.log (183 / 512)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (495553343 / 1000000000) ≤ -Real.log (1280 / 2101) ∧
    -Real.log (1280 / 2101) ≤ (7743021 / 15625000) := by
  have h := checkLog_sound (w := (821 / 3381)) (n := 12)
    (lo := (495553343 / 1000000000)) (hi := (7743021 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2101 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2101 / 1280) = 1/(1280 / 2101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (495553343 / 1000000000) (7743021 / 15625000) (Real.log (2101 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2101 / 1280) = -Real.log (1280 / 2101) := by
    rw [show ((2101 / 1280) : ℝ) = ((1280 / 2101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (512782573 / 500000000) ≤ -Real.log (459 / 1280) ∧
    -Real.log (459 / 1280) ≤ (256391287 / 250000000) := by
  have h := checkLog_sound (w := (181 / 1099)) (n := 12)
    (lo := (166208983 / 500000000)) (hi := (332417967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 459) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 459) = 1/(459 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-256391287 / 250000000) (-512782573 / 500000000) (Real.log (459 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (190261307 / 500000000) ≤ -Real.log (1000000 / 1463049) ∧
    -Real.log (1000000 / 1463049) ≤ (76104523 / 200000000) := by
  have h := checkLog_sound (w := (463049 / 2463049)) (n := 12)
    (lo := (190261307 / 500000000)) (hi := (76104523 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1463049 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1463049 / 1000000) = 1/(1000000 / 1463049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (190261307 / 500000000) (76104523 / 200000000) (Real.log (1463049 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1463049 / 1000000) = -Real.log (1000000 / 1463049) := by
    rw [show ((1463049 / 1000000) : ℝ) = ((1000000 / 1463049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (155462109 / 250000000) ≤ -Real.log (536951 / 1000000) ∧
    -Real.log (536951 / 1000000) ≤ (621848437 / 1000000000) := by
  have h := checkLog_sound (w := (463049 / 1536951)) (n := 12)
    (lo := (155462109 / 250000000)) (hi := (621848437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 536951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 536951) = 1/(536951 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-621848437 / 1000000000) (-155462109 / 250000000) (Real.log (536951 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (95282687 / 250000000) ≤ -Real.log (1000000 / 1463939) ∧
    -Real.log (1000000 / 1463939) ≤ (381130749 / 1000000000) := by
  have h := checkLog_sound (w := (463939 / 2463939)) (n := 12)
    (lo := (95282687 / 250000000)) (hi := (381130749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1463939 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1463939 / 1000000) = 1/(1000000 / 1463939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (95282687 / 250000000) (381130749 / 1000000000) (Real.log (1463939 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1463939 / 1000000) = -Real.log (1000000 / 1463939) := by
    rw [show ((1463939 / 1000000) : ℝ) = ((1000000 / 1463939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (311753659 / 500000000) ≤ -Real.log (536061 / 1000000) ∧
    -Real.log (536061 / 1000000) ≤ (623507319 / 1000000000) := by
  have h := checkLog_sound (w := (463939 / 1536061)) (n := 12)
    (lo := (311753659 / 500000000)) (hi := (623507319 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 536061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 536061) = 1/(536061 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-623507319 / 1000000000) (-311753659 / 500000000) (Real.log (536061 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (2986413 / 10000000) ≤ -Real.log (500000 / 674013) ∧
    -Real.log (500000 / 674013) ≤ (298641301 / 1000000000) := by
  have h := checkLog_sound (w := (174013 / 1174013)) (n := 12)
    (lo := (2986413 / 10000000)) (hi := (298641301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((674013 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(674013 / 500000) = 1/(500000 / 674013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (2986413 / 10000000) (298641301 / 1000000000) (Real.log (674013 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (674013 / 500000) = -Real.log (500000 / 674013) := by
    rw [show ((674013 / 500000) : ℝ) = ((500000 / 674013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (85550119 / 200000000) ≤ -Real.log (325987 / 500000) ∧
    -Real.log (325987 / 500000) ≤ (106937649 / 250000000) := by
  have h := checkLog_sound (w := (174013 / 825987)) (n := 12)
    (lo := (85550119 / 200000000)) (hi := (106937649 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 325987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 325987) = 1/(325987 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-106937649 / 250000000) (-85550119 / 200000000) (Real.log (325987 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (1870003 / 6250000) ≤ -Real.log (50000 / 67439) ∧
    -Real.log (50000 / 67439) ≤ (299200481 / 1000000000) := by
  have h := checkLog_sound (w := (17439 / 117439)) (n := 12)
    (lo := (1870003 / 6250000)) (hi := (299200481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67439 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67439 / 50000) = 1/(50000 / 67439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (1870003 / 6250000) (299200481 / 1000000000) (Real.log (67439 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (67439 / 50000) = -Real.log (50000 / 67439) := by
    rw [show ((67439 / 50000) : ℝ) = ((50000 / 67439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (53613469 / 125000000) ≤ -Real.log (32561 / 50000) ∧
    -Real.log (32561 / 50000) ≤ (428907753 / 1000000000) := by
  have h := checkLog_sound (w := (17439 / 82561)) (n := 12)
    (lo := (53613469 / 125000000)) (hi := (428907753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 32561) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 32561) = 1/(32561 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-428907753 / 1000000000) (-53613469 / 125000000) (Real.log (32561 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (20047421 / 20000000) ≤ -Real.log (500000000000 / 1362367329607) ∧
    -Real.log (500000000000 / 1362367329607) ≤ (250592763 / 250000000) := by
  have h := checkLog_sound (w := (362367329607 / 2362367329607)) (n := 12)
    (lo := (30922387 / 100000000)) (hi := (309223871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1362367329607 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1362367329607 / 1000000000000) = 1/(500000000000 / 1362367329607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (20047421 / 20000000) (250592763 / 250000000) (Real.log (1362367329607 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1362367329607 / 500000000000) = -Real.log (500000000000 / 1362367329607) := by
    rw [show ((1362367329607 / 500000000000) : ℝ) = ((500000000000 / 1362367329607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (200927613 / 200000000) ≤ -Real.log (500000000000 / 1365459341381) ∧
    -Real.log (500000000000 / 1365459341381) ≤ (1004638067 / 1000000000) := by
  have h := checkLog_sound (w := (365459341381 / 2365459341381)) (n := 12)
    (lo := (62298177 / 200000000)) (hi := (155745443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1365459341381 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1365459341381 / 1000000000000) = 1/(500000000000 / 1365459341381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (200927613 / 200000000) (1004638067 / 1000000000) (Real.log (1365459341381 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1365459341381 / 500000000000) = -Real.log (500000000000 / 1365459341381) := by
    rw [show ((1365459341381 / 500000000000) : ℝ) = ((500000000000 / 1365459341381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (363195947 / 500000000) ≤ -Real.log (500000000000 / 1033803495231) ∧
    -Real.log (500000000000 / 1033803495231) ≤ (90798987 / 125000000) := by
  have h := checkLog_sound (w := (33803495231 / 2033803495231)) (n := 12)
    (lo := (16622357 / 500000000)) (hi := (6648943 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1033803495231 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1033803495231 / 1000000000000) = 1/(500000000000 / 1033803495231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (363195947 / 500000000) (90798987 / 125000000) (Real.log (1033803495231 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1033803495231 / 500000000000) = -Real.log (500000000000 / 1033803495231) := by
    rw [show ((1033803495231 / 500000000000) : ℝ) = ((500000000000 / 1033803495231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (728108231 / 1000000000) ≤ -Real.log (250000000000 / 517789687049) ∧
    -Real.log (250000000000 / 517789687049) ≤ (728108233 / 1000000000) := by
  have h := checkLog_sound (w := (17789687049 / 1017789687049)) (n := 12)
    (lo := (34961051 / 1000000000)) (hi := (8740263 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((517789687049 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(517789687049 / 500000000000) = 1/(250000000000 / 517789687049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (728108231 / 1000000000) (728108233 / 1000000000) (Real.log (517789687049 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (517789687049 / 250000000000) = -Real.log (250000000000 / 517789687049) := by
    rw [show ((517789687049 / 250000000000) : ℝ) = ((250000000000 / 517789687049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0171
