import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell069
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

theorem reflection_log_1_neg : (127714607 / 500000000) ≤ -Real.log (512 / 661) ∧
    -Real.log (512 / 661) ≤ (51085843 / 200000000) := by
  have h := checkLog_sound (w := (149 / 1173)) (n := 12)
    (lo := (127714607 / 500000000)) (hi := (51085843 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((661 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(661 / 512) = 1/(512 / 661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (127714607 / 500000000) (51085843 / 200000000) (Real.log (661 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (661 / 512) = -Real.log (512 / 661) := by
    rw [show ((661 / 512) : ℝ) = ((512 / 661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (34392179 / 100000000) ≤ -Real.log (363 / 512) ∧
    -Real.log (363 / 512) ≤ (343921791 / 1000000000) := by
  have h := checkLog_sound (w := (149 / 875)) (n := 12)
    (lo := (34392179 / 100000000)) (hi := (343921791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 363) = 1/(363 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-343921791 / 1000000000) (-34392179 / 100000000) (Real.log (363 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (254975253 / 1000000000) ≤ -Real.log (5120 / 6607) ∧
    -Real.log (5120 / 6607) ≤ (127487627 / 500000000) := by
  have h := checkLog_sound (w := (1487 / 11727)) (n := 12)
    (lo := (254975253 / 1000000000)) (hi := (127487627 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6607 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6607 / 5120) = 1/(5120 / 6607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (254975253 / 1000000000) (127487627 / 500000000) (Real.log (6607 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6607 / 5120) = -Real.log (5120 / 6607) := by
    rw [show ((6607 / 5120) : ℝ) = ((5120 / 6607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (68619137 / 200000000) ≤ -Real.log (3633 / 5120) ∧
    -Real.log (3633 / 5120) ≤ (171547843 / 500000000) := by
  have h := checkLog_sound (w := (1487 / 8753)) (n := 12)
    (lo := (68619137 / 200000000)) (hi := (171547843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3633) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3633) = 1/(3633 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-171547843 / 500000000) (-68619137 / 200000000) (Real.log (3633 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (93700981 / 500000000) ≤ -Real.log (31250 / 37691) ∧
    -Real.log (31250 / 37691) ≤ (187401963 / 1000000000) := by
  have h := checkLog_sound (w := (6441 / 68941)) (n := 12)
    (lo := (93700981 / 500000000)) (hi := (187401963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37691 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37691 / 31250) = 1/(31250 / 37691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (93700981 / 500000000) (187401963 / 1000000000) (Real.log (37691 / 31250)) := by
  have h := reflection_log_5_neg
  have he : Real.log (37691 / 31250) = -Real.log (31250 / 37691) := by
    rw [show ((37691 / 31250) : ℝ) = ((31250 / 37691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (46162577 / 200000000) ≤ -Real.log (24809 / 31250) ∧
    -Real.log (24809 / 31250) ≤ (115406443 / 500000000) := by
  have h := checkLog_sound (w := (6441 / 56059)) (n := 12)
    (lo := (46162577 / 200000000)) (hi := (115406443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 24809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 24809) = 1/(24809 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-115406443 / 500000000) (-46162577 / 200000000) (Real.log (24809 / 31250)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (11734383 / 62500000) ≤ -Real.log (250000 / 301633) ∧
    -Real.log (250000 / 301633) ≤ (187750129 / 1000000000) := by
  have h := checkLog_sound (w := (51633 / 551633)) (n := 12)
    (lo := (11734383 / 62500000)) (hi := (187750129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301633 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301633 / 250000) = 1/(250000 / 301633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (11734383 / 62500000) (187750129 / 1000000000) (Real.log (301633 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (301633 / 250000) = -Real.log (250000 / 301633) := by
    rw [show ((301633 / 250000) : ℝ) = ((250000 / 301633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (231342067 / 1000000000) ≤ -Real.log (198367 / 250000) ∧
    -Real.log (198367 / 250000) ≤ (57835517 / 250000000) := by
  have h := checkLog_sound (w := (51633 / 448367)) (n := 12)
    (lo := (231342067 / 1000000000)) (hi := (57835517 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 198367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 198367) = 1/(198367 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-57835517 / 250000000) (-231342067 / 1000000000) (Real.log (198367 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (137568233 / 1000000000) ≤ -Real.log (25000 / 28687) ∧
    -Real.log (25000 / 28687) ≤ (68784117 / 500000000) := by
  have h := checkLog_sound (w := (3687 / 53687)) (n := 12)
    (lo := (137568233 / 1000000000)) (hi := (68784117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28687 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28687 / 25000) = 1/(25000 / 28687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (137568233 / 1000000000) (68784117 / 500000000) (Real.log (28687 / 25000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (28687 / 25000) = -Real.log (25000 / 28687) := by
    rw [show ((28687 / 25000) : ℝ) = ((25000 / 28687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (159558609 / 1000000000) ≤ -Real.log (21313 / 25000) ∧
    -Real.log (21313 / 25000) ≤ (15955861 / 100000000) := by
  have h := checkLog_sound (w := (3687 / 46313)) (n := 12)
    (lo := (159558609 / 1000000000)) (hi := (15955861 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 21313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 21313) = 1/(21313 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-15955861 / 100000000) (-159558609 / 1000000000) (Real.log (21313 / 25000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (137836611 / 1000000000) ≤ -Real.log (250000 / 286947) ∧
    -Real.log (250000 / 286947) ≤ (34459153 / 250000000) := by
  have h := checkLog_sound (w := (36947 / 536947)) (n := 12)
    (lo := (137836611 / 1000000000)) (hi := (34459153 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((286947 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(286947 / 250000) = 1/(250000 / 286947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (137836611 / 1000000000) (34459153 / 250000000) (Real.log (286947 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (286947 / 250000) = -Real.log (250000 / 286947) := by
    rw [show ((286947 / 250000) : ℝ) = ((250000 / 286947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (39979989 / 250000000) ≤ -Real.log (213053 / 250000) ∧
    -Real.log (213053 / 250000) ≤ (159919957 / 1000000000) := by
  have h := checkLog_sound (w := (36947 / 463053)) (n := 12)
    (lo := (39979989 / 250000000)) (hi := (159919957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 213053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 213053) = 1/(213053 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-159919957 / 1000000000) (-39979989 / 250000000) (Real.log (213053 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (598070939 / 1000000000) ≤ -Real.log (100000000000 / 181860721167) ∧
    -Real.log (100000000000 / 181860721167) ≤ (29903547 / 50000000) := by
  have h := checkLog_sound (w := (81860721167 / 281860721167)) (n := 12)
    (lo := (598070939 / 1000000000)) (hi := (29903547 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181860721167 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181860721167 / 100000000000) = 1/(100000000000 / 181860721167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (598070939 / 1000000000) (29903547 / 50000000) (Real.log (181860721167 / 100000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (181860721167 / 100000000000) = -Real.log (100000000000 / 181860721167) := by
    rw [show ((181860721167 / 100000000000) : ℝ) = ((100000000000 / 181860721167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (119870201 / 200000000) ≤ -Real.log (12500000000 / 22761707989) ∧
    -Real.log (12500000000 / 22761707989) ≤ (299675503 / 500000000) := by
  have h := checkLog_sound (w := (10261707989 / 35261707989)) (n := 12)
    (lo := (119870201 / 200000000)) (hi := (299675503 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22761707989 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(22761707989 / 12500000000) = 1/(12500000000 / 22761707989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (119870201 / 200000000) (299675503 / 500000000) (Real.log (22761707989 / 12500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (22761707989 / 12500000000) = -Real.log (12500000000 / 22761707989) := by
    rw [show ((22761707989 / 12500000000) : ℝ) = ((12500000000 / 22761707989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (6534607 / 15625000) ≤ -Real.log (500000000000 / 759623523721) ∧
    -Real.log (500000000000 / 759623523721) ≤ (418214849 / 1000000000) := by
  have h := checkLog_sound (w := (259623523721 / 1259623523721)) (n := 12)
    (lo := (6534607 / 15625000)) (hi := (418214849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((759623523721 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(759623523721 / 500000000000) = 1/(500000000000 / 759623523721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (6534607 / 15625000) (418214849 / 1000000000) (Real.log (759623523721 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (759623523721 / 500000000000) = -Real.log (500000000000 / 759623523721) := by
    rw [show ((759623523721 / 500000000000) : ℝ) = ((500000000000 / 759623523721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (104773049 / 250000000) ≤ -Real.log (100000000000 / 152058054011) ∧
    -Real.log (100000000000 / 152058054011) ≤ (419092197 / 1000000000) := by
  have h := checkLog_sound (w := (52058054011 / 252058054011)) (n := 12)
    (lo := (104773049 / 250000000)) (hi := (419092197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((152058054011 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(152058054011 / 100000000000) = 1/(100000000000 / 152058054011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (104773049 / 250000000) (419092197 / 1000000000) (Real.log (152058054011 / 100000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (152058054011 / 100000000000) = -Real.log (100000000000 / 152058054011) := by
    rw [show ((152058054011 / 100000000000) : ℝ) = ((100000000000 / 152058054011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (297126843 / 1000000000) ≤ -Real.log (500000000000 / 672993008961) ∧
    -Real.log (500000000000 / 672993008961) ≤ (74281711 / 250000000) := by
  have h := checkLog_sound (w := (172993008961 / 1172993008961)) (n := 12)
    (lo := (297126843 / 1000000000)) (hi := (74281711 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((672993008961 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(672993008961 / 500000000000) = 1/(500000000000 / 672993008961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (297126843 / 1000000000) (74281711 / 250000000) (Real.log (672993008961 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (672993008961 / 500000000000) = -Real.log (500000000000 / 672993008961) := by
    rw [show ((672993008961 / 500000000000) : ℝ) = ((500000000000 / 672993008961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (37219571 / 125000000) ≤ -Real.log (250000000000 / 336708471601) ∧
    -Real.log (250000000000 / 336708471601) ≤ (297756569 / 1000000000) := by
  have h := checkLog_sound (w := (86708471601 / 586708471601)) (n := 12)
    (lo := (37219571 / 125000000)) (hi := (297756569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336708471601 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(336708471601 / 250000000000) = 1/(250000000000 / 336708471601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (37219571 / 125000000) (297756569 / 1000000000) (Real.log (336708471601 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (336708471601 / 250000000000) = -Real.log (250000000000 / 336708471601) := by
    rw [show ((336708471601 / 250000000000) : ℝ) = ((250000000000 / 336708471601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1380209 / 62500000) ≤ -Real.log (61134919191 / 62500000000) ∧
    -Real.log (61134919191 / 62500000000) ≤ (4416669 / 200000000) := by
  have h := checkLog_sound (w := (1365080809 / 123634919191)) (n := 12)
    (lo := (1380209 / 62500000)) (hi := (4416669 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61134919191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61134919191) = 1/(61134919191 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-4416669 / 200000000) (-1380209 / 62500000) (Real.log (61134919191 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (2748797 / 125000000) ≤ -Real.log (611406031 / 625000000) ∧
    -Real.log (611406031 / 625000000) ≤ (21990377 / 1000000000) := by
  have h := checkLog_sound (w := (13593969 / 1236406031)) (n := 12)
    (lo := (2748797 / 125000000)) (hi := (21990377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 611406031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 611406031) = 1/(611406031 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-21990377 / 1000000000) (-2748797 / 125000000) (Real.log (611406031 / 625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell069
