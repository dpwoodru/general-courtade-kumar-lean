import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0014
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

theorem reflection_log_1_neg : (136488131 / 200000000) ≤ -Real.log (102400 / 202619) ∧
    -Real.log (102400 / 202619) ≤ (42652541 / 62500000) := by
  have h := checkLog_sound (w := (100219 / 305019)) (n := 12)
    (lo := (136488131 / 200000000)) (hi := (42652541 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202619 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202619 / 102400) = 1/(102400 / 202619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (136488131 / 200000000) (42652541 / 62500000) (Real.log (202619 / 102400)) := by
  have h := reflection_log_1_neg
  have he : Real.log (202619 / 102400) = -Real.log (102400 / 202619) := by
    rw [show ((202619 / 102400) : ℝ) = ((102400 / 202619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1924551611 / 500000000) ≤ -Real.log (2181 / 102400) ∧
    -Real.log (2181 / 102400) ≤ (962275807 / 250000000) := by
  have h := checkLog_sound (w := (1019 / 5381)) (n := 12)
    (lo := (191683661 / 500000000)) (hi := (383367323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2181) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2181) = 1/(2181 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-962275807 / 250000000) (-1924551611 / 500000000) (Real.log (2181 / 102400)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (682346879 / 1000000000) ≤ -Real.log (512 / 1013) ∧
    -Real.log (512 / 1013) ≤ (1066167 / 1562500) := by
  have h := checkLog_sound (w := (501 / 1525)) (n := 12)
    (lo := (682346879 / 1000000000)) (hi := (1066167 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1013 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1013 / 512) = 1/(512 / 1013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (682346879 / 1000000000) (1066167 / 1562500) (Real.log (1013 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1013 / 512) = -Real.log (512 / 1013) := by
    rw [show ((1013 / 512) : ℝ) = ((512 / 1013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3840429349 / 1000000000) ≤ -Real.log (11 / 512) ∧
    -Real.log (11 / 512) ≤ (768085871 / 200000000) := by
  have h := checkLog_sound (w := (5 / 27)) (n := 12)
    (lo := (374693449 / 1000000000)) (hi := (7493869 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 11) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(16 / 11) = 1/(11 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-768085871 / 200000000) (-3840429349 / 1000000000) (Real.log (11 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (671618259 / 1000000000) ≤ -Real.log (51200 / 100219) ∧
    -Real.log (51200 / 100219) ≤ (33580913 / 50000000) := by
  have h := checkLog_sound (w := (49019 / 151419)) (n := 12)
    (lo := (671618259 / 1000000000)) (hi := (33580913 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100219 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100219 / 51200) = 1/(51200 / 100219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (671618259 / 1000000000) (33580913 / 50000000) (Real.log (100219 / 51200)) := by
  have h := reflection_log_5_neg
  have he : Real.log (100219 / 51200) = -Real.log (51200 / 100219) := by
    rw [show ((100219 / 51200) : ℝ) = ((51200 / 100219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1577978021 / 500000000) ≤ -Real.log (2181 / 51200) ∧
    -Real.log (2181 / 51200) ≤ (3155956047 / 1000000000) := by
  have h := checkLog_sound (w := (1019 / 5381)) (n := 12)
    (lo := (191683661 / 500000000)) (hi := (383367323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2181) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2181) = 1/(2181 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3155956047 / 1000000000) (-1577978021 / 500000000) (Real.log (2181 / 51200)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (41964291 / 62500000) ≤ -Real.log (256 / 501) ∧
    -Real.log (256 / 501) ≤ (671428657 / 1000000000) := by
  have h := checkLog_sound (w := (245 / 757)) (n := 12)
    (lo := (41964291 / 62500000)) (hi := (671428657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((501 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(501 / 256) = 1/(256 / 501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (41964291 / 62500000) (671428657 / 1000000000) (Real.log (501 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (501 / 256) = -Real.log (256 / 501) := by
    rw [show ((501 / 256) : ℝ) = ((256 / 501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3147282169 / 1000000000) ≤ -Real.log (11 / 256) ∧
    -Real.log (11 / 256) ≤ (1573641087 / 500000000) := by
  have h := checkLog_sound (w := (5 / 27)) (n := 12)
    (lo := (374693449 / 1000000000)) (hi := (7493869 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 11) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(16 / 11) = 1/(11 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1573641087 / 500000000) (-3147282169 / 1000000000) (Real.log (11 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (683992907 / 1000000000) ≤ -Real.log (40000 / 79271) ∧
    -Real.log (40000 / 79271) ≤ (170998227 / 250000000) := by
  have h := checkLog_sound (w := (39271 / 119271)) (n := 12)
    (lo := (683992907 / 1000000000)) (hi := (170998227 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79271 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79271 / 40000) = 1/(40000 / 79271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (683992907 / 1000000000) (170998227 / 250000000) (Real.log (79271 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (79271 / 40000) = -Real.log (40000 / 79271) := by
    rw [show ((79271 / 40000) : ℝ) = ((40000 / 79271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (2002480499 / 500000000) ≤ -Real.log (729 / 40000) ∧
    -Real.log (729 / 40000) ≤ (1001240251 / 250000000) := by
  have h := checkLog_sound (w := (521 / 1979)) (n := 12)
    (lo := (269612549 / 500000000)) (hi := (539225099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 729) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1250 / 729) = 1/(729 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1001240251 / 250000000) (-2002480499 / 500000000) (Real.log (729 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (684069603 / 1000000000) ≤ -Real.log (1000000 / 1981927) ∧
    -Real.log (1000000 / 1981927) ≤ (171017401 / 250000000) := by
  have h := checkLog_sound (w := (981927 / 2981927)) (n := 12)
    (lo := (684069603 / 1000000000)) (hi := (171017401 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981927 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981927 / 1000000) = 1/(1000000 / 1981927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (684069603 / 1000000000) (171017401 / 250000000) (Real.log (1981927 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1981927 / 1000000) = -Real.log (1000000 / 1981927) := by
    rw [show ((1981927 / 1000000) : ℝ) = ((1000000 / 1981927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1003334041 / 250000000) ≤ -Real.log (18073 / 1000000) ∧
    -Real.log (18073 / 1000000) ≤ (401333617 / 100000000) := by
  have h := checkLog_sound (w := (13177 / 49323)) (n := 12)
    (lo := (68450033 / 125000000)) (hi := (109520053 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18073) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 18073) = 1/(18073 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-401333617 / 100000000) (-1003334041 / 250000000) (Real.log (18073 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (21373643 / 31250000) ≤ -Real.log (1000000 / 1981703) ∧
    -Real.log (1000000 / 1981703) ≤ (683956577 / 1000000000) := by
  have h := checkLog_sound (w := (981703 / 2981703)) (n := 12)
    (lo := (21373643 / 31250000)) (hi := (683956577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981703 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981703 / 1000000) = 1/(1000000 / 1981703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (21373643 / 31250000) (683956577 / 1000000000) (Real.log (1981703 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1981703 / 1000000) = -Real.log (1000000 / 1981703) := by
    rw [show ((1981703 / 1000000) : ℝ) = ((1000000 / 1981703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1000254541 / 250000000) ≤ -Real.log (18297 / 1000000) ∧
    -Real.log (18297 / 1000000) ≤ (400101817 / 100000000) := by
  have h := checkLog_sound (w := (12953 / 49547)) (n := 12)
    (lo := (66910283 / 125000000)) (hi := (107056453 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18297) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 18297) = 1/(18297 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-400101817 / 100000000) (-1000254541 / 250000000) (Real.log (18297 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (684034283 / 1000000000) ≤ -Real.log (1000000 / 1981857) ∧
    -Real.log (1000000 / 1981857) ≤ (171008571 / 250000000) := by
  have h := checkLog_sound (w := (981857 / 2981857)) (n := 12)
    (lo := (684034283 / 1000000000)) (hi := (171008571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981857 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981857 / 1000000) = 1/(1000000 / 1981857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (684034283 / 1000000000) (171008571 / 250000000) (Real.log (1981857 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1981857 / 1000000) = -Real.log (1000000 / 1981857) := by
    rw [show ((1981857 / 1000000) : ℝ) = ((1000000 / 1981857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (7830997 / 1953125) ≤ -Real.log (18143 / 1000000) ∧
    -Real.log (18143 / 1000000) ≤ (400947047 / 100000000) := by
  have h := checkLog_sound (w := (13107 / 49393)) (n := 12)
    (lo := (135933641 / 250000000)) (hi := (108746913 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18143) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 18143) = 1/(18143 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-400947047 / 100000000) (-7830997 / 1953125) (Real.log (18143 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (937790781 / 200000000) ≤ -Real.log (250000000000 / 27184842249657) ∧
    -Real.log (250000000000 / 27184842249657) ≤ (586119239 / 125000000) := by
  have h := checkLog_sound (w := (11184842249657 / 43184842249657)) (n := 12)
    (lo := (21202833 / 40000000)) (hi := (265035413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27184842249657 / 16000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(27184842249657 / 16000000000000) = 1/(250000000000 / 27184842249657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (937790781 / 200000000) (586119239 / 125000000) (Real.log (27184842249657 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (27184842249657 / 250000000000) = -Real.log (250000000000 / 27184842249657) := by
    rw [show ((27184842249657 / 250000000000) : ℝ) = ((250000000000 / 27184842249657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4697405767 / 1000000000) ≤ -Real.log (500000000000 / 54831156974493) ∧
    -Real.log (500000000000 / 54831156974493) ≤ (2348702887 / 500000000) := by
  have h := checkLog_sound (w := (22831156974493 / 86831156974493)) (n := 12)
    (lo := (538522687 / 1000000000)) (hi := (8414417 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54831156974493 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(54831156974493 / 32000000000000) = 1/(500000000000 / 54831156974493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4697405767 / 1000000000) (2348702887 / 500000000) (Real.log (54831156974493 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (54831156974493 / 500000000000) = -Real.log (500000000000 / 54831156974493) := by
    rw [show ((54831156974493 / 500000000000) : ℝ) = ((500000000000 / 54831156974493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (4684974739 / 1000000000) ≤ -Real.log (500000000000 / 54153768377329) ∧
    -Real.log (500000000000 / 54153768377329) ≤ (2342487373 / 500000000) := by
  have h := checkLog_sound (w := (22153768377329 / 86153768377329)) (n := 12)
    (lo := (526091659 / 1000000000)) (hi := (26304583 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54153768377329 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(54153768377329 / 32000000000000) = 1/(500000000000 / 54153768377329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (4684974739 / 1000000000) (2342487373 / 500000000) (Real.log (54153768377329 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (54153768377329 / 500000000000) = -Real.log (500000000000 / 54153768377329) := by
    rw [show ((54153768377329 / 500000000000) : ℝ) = ((500000000000 / 54153768377329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1173376187 / 250000000) ≤ -Real.log (50000000000 / 5461767623877) ∧
    -Real.log (50000000000 / 5461767623877) ≤ (938700951 / 200000000) := by
  have h := checkLog_sound (w := (2261767623877 / 8661767623877)) (n := 12)
    (lo := (133655417 / 250000000)) (hi := (534621669 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5461767623877 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5461767623877 / 3200000000000) = 1/(50000000000 / 5461767623877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1173376187 / 250000000) (938700951 / 200000000) (Real.log (5461767623877 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (5461767623877 / 50000000000) = -Real.log (50000000000 / 5461767623877) := by
    rw [show ((5461767623877 / 50000000000) : ℝ) = ((50000000000 / 5461767623877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0014
