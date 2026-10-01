import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0015
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

theorem reflection_log_1_neg : (682346879 / 1000000000) ≤ -Real.log (512 / 1013) ∧
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


theorem reflection_log_1 : Bounds (682346879 / 1000000000) (1066167 / 1562500) (Real.log (1013 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1013 / 512) = -Real.log (512 / 1013) := by
    rw [show ((1013 / 512) : ℝ) = ((512 / 1013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3840429349 / 1000000000) ≤ -Real.log (11 / 512) ∧
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


theorem reflection_log_2 : Bounds (-768085871 / 200000000) (-3840429349 / 1000000000) (Real.log (11 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (682253093 / 1000000000) ≤ -Real.log (102400 / 202581) ∧
    -Real.log (102400 / 202581) ≤ (341126547 / 500000000) := by
  have h := checkLog_sound (w := (100181 / 304981)) (n := 12)
    (lo := (682253093 / 1000000000)) (hi := (341126547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202581 / 102400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202581 / 102400) = 1/(102400 / 202581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (682253093 / 1000000000) (341126547 / 500000000) (Real.log (202581 / 102400)) := by
  have h := reflection_log_3_neg
  have he : Real.log (202581 / 102400) = -Real.log (102400 / 202581) := by
    rw [show ((202581 / 102400) : ℝ) = ((102400 / 202581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (766366013 / 200000000) ≤ -Real.log (2219 / 102400) ∧
    -Real.log (2219 / 102400) ≤ (3831830071 / 1000000000) := by
  have h := checkLog_sound (w := (981 / 5419)) (n := 12)
    (lo := (73218833 / 200000000)) (hi := (183047083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2219) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(3200 / 2219) = 1/(2219 / 102400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-3831830071 / 1000000000) (-766366013 / 200000000) (Real.log (2219 / 102400)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (41964291 / 62500000) ≤ -Real.log (256 / 501) ∧
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


theorem reflection_log_5 : Bounds (41964291 / 62500000) (671428657 / 1000000000) (Real.log (501 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (501 / 256) = -Real.log (256 / 501) := by
    rw [show ((501 / 256) : ℝ) = ((256 / 501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (3147282169 / 1000000000) ≤ -Real.log (11 / 256) ∧
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


theorem reflection_log_6 : Bounds (-1573641087 / 500000000) (-3147282169 / 1000000000) (Real.log (11 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (671239017 / 1000000000) ≤ -Real.log (51200 / 100181) ∧
    -Real.log (51200 / 100181) ≤ (335619509 / 500000000) := by
  have h := checkLog_sound (w := (48981 / 151381)) (n := 12)
    (lo := (671239017 / 1000000000)) (hi := (335619509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100181 / 51200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100181 / 51200) = 1/(51200 / 100181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (671239017 / 1000000000) (335619509 / 500000000) (Real.log (100181 / 51200)) := by
  have h := reflection_log_7_neg
  have he : Real.log (100181 / 51200) = -Real.log (51200 / 100181) := by
    rw [show ((100181 / 51200) : ℝ) = ((51200 / 100181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (627736577 / 200000000) ≤ -Real.log (2219 / 51200) ∧
    -Real.log (2219 / 51200) ≤ (313868289 / 100000000) := by
  have h := checkLog_sound (w := (981 / 5419)) (n := 12)
    (lo := (73218833 / 200000000)) (hi := (183047083 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3200 / 2219) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3200 / 2219) = 1/(2219 / 51200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-313868289 / 100000000) (-627736577 / 200000000) (Real.log (2219 / 51200)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (68391671 / 100000000) ≤ -Real.log (125000 / 247703) ∧
    -Real.log (125000 / 247703) ≤ (683916711 / 1000000000) := by
  have h := checkLog_sound (w := (122703 / 372703)) (n := 12)
    (lo := (68391671 / 100000000)) (hi := (683916711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247703 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247703 / 125000) = 1/(125000 / 247703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (68391671 / 100000000) (683916711 / 1000000000) (Real.log (247703 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (247703 / 125000) = -Real.log (125000 / 247703) := by
    rw [show ((247703 / 125000) : ℝ) = ((125000 / 247703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (399670981 / 100000000) ≤ -Real.log (2297 / 125000) ∧
    -Real.log (2297 / 125000) ≤ (499588727 / 125000000) := by
  have h := checkLog_sound (w := (6437 / 24813)) (n := 12)
    (lo := (53097391 / 100000000)) (hi := (530973911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9188) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9188) = 1/(2297 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-499588727 / 125000000) (-399670981 / 100000000) (Real.log (2297 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (170998353 / 250000000) ≤ -Real.log (62500 / 123861) ∧
    -Real.log (62500 / 123861) ≤ (683993413 / 1000000000) := by
  have h := checkLog_sound (w := (61361 / 186361)) (n := 12)
    (lo := (170998353 / 250000000)) (hi := (683993413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123861 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123861 / 62500) = 1/(62500 / 123861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (170998353 / 250000000) (683993413 / 1000000000) (Real.log (123861 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (123861 / 62500) = -Real.log (62500 / 123861) := by
    rw [show ((123861 / 62500) : ℝ) = ((62500 / 123861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (4005015869 / 1000000000) ≤ -Real.log (1139 / 62500) ∧
    -Real.log (1139 / 62500) ≤ (32040127 / 8000000) := by
  have h := checkLog_sound (w := (6513 / 24737)) (n := 12)
    (lo := (539279969 / 1000000000)) (hi := (53927997 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9112) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9112) = 1/(1139 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-32040127 / 8000000) (-4005015869 / 1000000000) (Real.log (1139 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (683879871 / 1000000000) ≤ -Real.log (1000000 / 1981551) ∧
    -Real.log (1000000 / 1981551) ≤ (10685623 / 15625000) := by
  have h := checkLog_sound (w := (981551 / 2981551)) (n := 12)
    (lo := (683879871 / 1000000000)) (hi := (10685623 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981551 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981551 / 1000000) = 1/(1000000 / 1981551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (683879871 / 1000000000) (10685623 / 15625000) (Real.log (1981551 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1981551 / 1000000) = -Real.log (1000000 / 1981551) := by
    rw [show ((1981551 / 1000000) : ℝ) = ((1000000 / 1981551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3992745107 / 1000000000) ≤ -Real.log (18449 / 1000000) ∧
    -Real.log (18449 / 1000000) ≤ (3992745113 / 1000000000) := by
  have h := checkLog_sound (w := (12801 / 49699)) (n := 12)
    (lo := (527009207 / 1000000000)) (hi := (65876151 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18449) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(31250 / 18449) = 1/(18449 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3992745113 / 1000000000) (-3992745107 / 1000000000) (Real.log (18449 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (17098927 / 25000000) ≤ -Real.log (125000 / 247713) ∧
    -Real.log (125000 / 247713) ≤ (683957081 / 1000000000) := by
  have h := checkLog_sound (w := (122713 / 372713)) (n := 12)
    (lo := (17098927 / 25000000)) (hi := (683957081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247713 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247713 / 125000) = 1/(125000 / 247713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (17098927 / 25000000) (683957081 / 1000000000) (Real.log (247713 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (247713 / 125000) = -Real.log (125000 / 247713) := by
    rw [show ((247713 / 125000) : ℝ) = ((125000 / 247713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (4001072819 / 1000000000) ≤ -Real.log (2287 / 125000) ∧
    -Real.log (2287 / 125000) ≤ (160042913 / 40000000) := by
  have h := checkLog_sound (w := (6477 / 24773)) (n := 12)
    (lo := (535336919 / 1000000000)) (hi := (13383423 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 9148) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(15625 / 9148) = 1/(2287 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-160042913 / 40000000) (-4001072819 / 1000000000) (Real.log (2287 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (117015663 / 25000000) ≤ -Real.log (500000000000 / 53918807139747) ∧
    -Real.log (500000000000 / 53918807139747) ≤ (4680626527 / 1000000000) := by
  have h := checkLog_sound (w := (21918807139747 / 85918807139747)) (n := 12)
    (lo := (6521793 / 12500000)) (hi := (521743441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53918807139747 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(53918807139747 / 32000000000000) = 1/(500000000000 / 53918807139747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (117015663 / 25000000) (4680626527 / 1000000000) (Real.log (53918807139747 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (53918807139747 / 500000000000) = -Real.log (500000000000 / 53918807139747) := by
    rw [show ((53918807139747 / 500000000000) : ℝ) = ((500000000000 / 53918807139747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4689009281 / 1000000000) ≤ -Real.log (125000000000 / 13593173836699) ∧
    -Real.log (125000000000 / 13593173836699) ≤ (586126161 / 125000000) := by
  have h := checkLog_sound (w := (5593173836699 / 21593173836699)) (n := 12)
    (lo := (530126201 / 1000000000)) (hi := (265063101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13593173836699 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(13593173836699 / 8000000000000) = 1/(125000000000 / 13593173836699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4689009281 / 1000000000) (586126161 / 125000000) (Real.log (13593173836699 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (13593173836699 / 125000000000) = -Real.log (125000000000 / 13593173836699) := by
    rw [show ((13593173836699 / 125000000000) : ℝ) = ((125000000000 / 13593173836699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (2338312489 / 500000000) ≤ -Real.log (500000000000 / 53703479863407) ∧
    -Real.log (500000000000 / 53703479863407) ≤ (935324997 / 200000000) := by
  have h := checkLog_sound (w := (21703479863407 / 85703479863407)) (n := 12)
    (lo := (258870949 / 500000000)) (hi := (517741899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((53703479863407 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(53703479863407 / 32000000000000) = 1/(500000000000 / 53703479863407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (2338312489 / 500000000) (935324997 / 200000000) (Real.log (53703479863407 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (53703479863407 / 500000000000) = -Real.log (500000000000 / 53703479863407) := by
    rw [show ((53703479863407 / 500000000000) : ℝ) = ((500000000000 / 53703479863407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (4685029899 / 1000000000) ≤ -Real.log (50000000000 / 5415675557499) ∧
    -Real.log (50000000000 / 5415675557499) ≤ (2342514953 / 500000000) := by
  have h := checkLog_sound (w := (2215675557499 / 8615675557499)) (n := 12)
    (lo := (526146819 / 1000000000)) (hi := (26307341 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5415675557499 / 3200000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5415675557499 / 3200000000000) = 1/(50000000000 / 5415675557499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (4685029899 / 1000000000) (2342514953 / 500000000) (Real.log (5415675557499 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (5415675557499 / 50000000000) = -Real.log (50000000000 / 5415675557499) := by
    rw [show ((5415675557499 / 50000000000) : ℝ) = ((50000000000 / 5415675557499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0015
