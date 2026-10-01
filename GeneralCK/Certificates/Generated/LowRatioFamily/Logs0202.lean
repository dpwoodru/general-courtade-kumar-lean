import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12928_neg : (659454093 / 500000000) ≤ -Real.log (100000000000 / 373933649289) ∧
    -Real.log (100000000000 / 373933649289) ≤ (329727047 / 250000000) := by
  have h := checkLog_sound (w := (173933649289 / 573933649289)) (n := 12)
    (lo := (312880503 / 500000000)) (hi := (625761007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373933649289 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(373933649289 / 200000000000) = 1/(100000000000 / 373933649289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12928 : Bounds (659454093 / 500000000) (329727047 / 250000000) (Real.log (373933649289 / 100000000000)) := by
  have h := reflection_log_12928_neg
  have he : Real.log (373933649289 / 100000000000) = -Real.log (100000000000 / 373933649289) := by
    rw [show ((373933649289 / 100000000000) : ℝ) = ((100000000000 / 373933649289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12929_neg : (331985479 / 250000000) ≤ -Real.log (500000000000 / 1886634844869) ∧
    -Real.log (500000000000 / 1886634844869) ≤ (663970959 / 500000000) := by
  have h := checkLog_sound (w := (886634844869 / 2886634844869)) (n := 12)
    (lo := (39674671 / 62500000)) (hi := (634794737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1886634844869 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1886634844869 / 1000000000000) = 1/(500000000000 / 1886634844869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12929 : Bounds (331985479 / 250000000) (663970959 / 500000000) (Real.log (1886634844869 / 500000000000)) := by
  have h := reflection_log_12929_neg
  have he : Real.log (1886634844869 / 500000000000) = -Real.log (500000000000 / 1886634844869) := by
    rw [show ((1886634844869 / 500000000000) : ℝ) = ((500000000000 / 1886634844869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12930_neg : (459953293 / 1000000000) ≤ -Real.log (125 / 198) ∧
    -Real.log (125 / 198) ≤ (229976647 / 500000000) := by
  have h := checkLog_sound (w := (73 / 323)) (n := 12)
    (lo := (459953293 / 1000000000)) (hi := (229976647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198 / 125) = 1/(125 / 198) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12930 : Bounds (459953293 / 1000000000) (229976647 / 500000000) (Real.log (198 / 125)) := by
  have h := reflection_log_12930_neg
  have he : Real.log (198 / 125) = -Real.log (125 / 198) := by
    rw [show ((198 / 125) : ℝ) = ((125 / 198) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12931_neg : (438535009 / 500000000) ≤ -Real.log (52 / 125) ∧
    -Real.log (52 / 125) ≤ (43853501 / 50000000) := by
  have h := checkLog_sound (w := (21 / 229)) (n := 12)
    (lo := (91961419 / 500000000)) (hi := (183922839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 104) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 104) = 1/(52 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12931 : Bounds (-43853501 / 50000000) (-438535009 / 500000000) (Real.log (52 / 125)) := by
  have h := reflection_log_12931_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12932_neg : (583829 / 1000000000) ≤ -Real.log (125000 / 125073) ∧
    -Real.log (125000 / 125073) ≤ (58383 / 100000000) := by
  have h := checkLog_sound (w := (73 / 250073)) (n := 12)
    (lo := (583829 / 1000000000)) (hi := (58383 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125073 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125073 / 125000) = 1/(125000 / 125073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12932 : Bounds (583829 / 1000000000) (58383 / 100000000) (Real.log (125073 / 125000)) := by
  have h := reflection_log_12932_neg
  have he : Real.log (125073 / 125000) = -Real.log (125000 / 125073) := by
    rw [show ((125073 / 125000) : ℝ) = ((125000 / 125073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12933_neg : (58417 / 100000000) ≤ -Real.log (124927 / 125000) ∧
    -Real.log (124927 / 125000) ≤ (584171 / 1000000000) := by
  have h := checkLog_sound (w := (73 / 249927)) (n := 12)
    (lo := (58417 / 100000000)) (hi := (584171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124927) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124927) = 1/(124927 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12933 : Bounds (-584171 / 1000000000) (-58417 / 100000000) (Real.log (124927 / 125000)) := by
  have h := reflection_log_12933_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12934_neg : (270008053 / 1000000000) ≤ -Real.log (40000 / 52399) ∧
    -Real.log (40000 / 52399) ≤ (135004027 / 500000000) := by
  have h := checkLog_sound (w := (12399 / 92399)) (n := 12)
    (lo := (270008053 / 1000000000)) (hi := (135004027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52399 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(52399 / 40000) = 1/(40000 / 52399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12934 : Bounds (270008053 / 1000000000) (135004027 / 500000000) (Real.log (52399 / 40000)) := by
  have h := reflection_log_12934_neg
  have he : Real.log (52399 / 40000) = -Real.log (40000 / 52399) := by
    rw [show ((52399 / 40000) : ℝ) = ((40000 / 52399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12935_neg : (7420549 / 20000000) ≤ -Real.log (27601 / 40000) ∧
    -Real.log (27601 / 40000) ≤ (371027451 / 1000000000) := by
  have h := checkLog_sound (w := (12399 / 67601)) (n := 12)
    (lo := (7420549 / 20000000)) (hi := (371027451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 27601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 27601) = 1/(27601 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12935 : Bounds (-371027451 / 1000000000) (-7420549 / 20000000) (Real.log (27601 / 40000)) := by
  have h := reflection_log_12935_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12936_neg : (271817899 / 1000000000) ≤ -Real.log (250000 / 328087) ∧
    -Real.log (250000 / 328087) ≤ (2718179 / 10000000) := by
  have h := checkLog_sound (w := (78087 / 578087)) (n := 12)
    (lo := (271817899 / 1000000000)) (hi := (2718179 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328087 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(328087 / 250000) = 1/(250000 / 328087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12936 : Bounds (271817899 / 1000000000) (2718179 / 10000000) (Real.log (328087 / 250000)) := by
  have h := reflection_log_12936_neg
  have he : Real.log (328087 / 250000) = -Real.log (250000 / 328087) := by
    rw [show ((328087 / 250000) : ℝ) = ((250000 / 328087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12937_neg : (187236191 / 500000000) ≤ -Real.log (171913 / 250000) ∧
    -Real.log (171913 / 250000) ≤ (374472383 / 1000000000) := by
  have h := checkLog_sound (w := (78087 / 421913)) (n := 12)
    (lo := (187236191 / 500000000)) (hi := (374472383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 171913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 171913) = 1/(171913 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12937 : Bounds (-374472383 / 1000000000) (-187236191 / 500000000) (Real.log (171913 / 250000)) := by
  have h := reflection_log_12937_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12938_neg : (102654483 / 1000000000) ≤ -Real.log (56402420431 / 62500000000) ∧
    -Real.log (56402420431 / 62500000000) ≤ (25663621 / 250000000) := by
  have h := checkLog_sound (w := (6097579569 / 118902420431)) (n := 12)
    (lo := (102654483 / 1000000000)) (hi := (25663621 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 56402420431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 56402420431) = 1/(56402420431 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12938 : Bounds (-25663621 / 250000000) (-102654483 / 1000000000) (Real.log (56402420431 / 62500000000)) := by
  have h := reflection_log_12938_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12939_neg : (101019397 / 1000000000) ≤ -Real.log (1446264799 / 1600000000) ∧
    -Real.log (1446264799 / 1600000000) ≤ (50509699 / 500000000) := by
  have h := checkLog_sound (w := (153735201 / 3046264799)) (n := 12)
    (lo := (101019397 / 1000000000)) (hi := (50509699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1446264799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1446264799) = 1/(1446264799 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12939 : Bounds (-50509699 / 500000000) (-101019397 / 1000000000) (Real.log (1446264799 / 1600000000)) := by
  have h := reflection_log_12939_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12940_neg : (641035503 / 1000000000) ≤ -Real.log (125000000000 / 237305713561) ∧
    -Real.log (125000000000 / 237305713561) ≤ (40064719 / 62500000) := by
  have h := checkLog_sound (w := (112305713561 / 362305713561)) (n := 12)
    (lo := (641035503 / 1000000000)) (hi := (40064719 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237305713561 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237305713561 / 125000000000) = 1/(125000000000 / 237305713561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12940 : Bounds (641035503 / 1000000000) (40064719 / 62500000) (Real.log (237305713561 / 125000000000)) := by
  have h := reflection_log_12940_neg
  have he : Real.log (237305713561 / 125000000000) = -Real.log (125000000000 / 237305713561) := by
    rw [show ((237305713561 / 125000000000) : ℝ) = ((125000000000 / 237305713561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12941_neg : (323145141 / 500000000) ≤ -Real.log (500000000000 / 954223938853) ∧
    -Real.log (500000000000 / 954223938853) ≤ (646290283 / 1000000000) := by
  have h := checkLog_sound (w := (454223938853 / 1454223938853)) (n := 12)
    (lo := (323145141 / 500000000)) (hi := (646290283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((954223938853 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(954223938853 / 500000000000) = 1/(500000000000 / 954223938853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12941 : Bounds (323145141 / 500000000) (646290283 / 1000000000) (Real.log (954223938853 / 500000000000)) := by
  have h := reflection_log_12941_neg
  have he : Real.log (954223938853 / 500000000000) = -Real.log (500000000000 / 954223938853) := by
    rw [show ((954223938853 / 500000000000) : ℝ) = ((500000000000 / 954223938853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12942_neg : (331985479 / 250000000) ≤ -Real.log (125000000000 / 471658711217) ∧
    -Real.log (125000000000 / 471658711217) ≤ (663970959 / 500000000) := by
  have h := checkLog_sound (w := (221658711217 / 721658711217)) (n := 12)
    (lo := (39674671 / 62500000)) (hi := (634794737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((471658711217 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(471658711217 / 250000000000) = 1/(125000000000 / 471658711217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12942 : Bounds (331985479 / 250000000) (663970959 / 500000000) (Real.log (471658711217 / 125000000000)) := by
  have h := reflection_log_12942_neg
  have he : Real.log (471658711217 / 125000000000) = -Real.log (125000000000 / 471658711217) := by
    rw [show ((471658711217 / 125000000000) : ℝ) = ((125000000000 / 471658711217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12943_neg : (1337023311 / 1000000000) ≤ -Real.log (500000000000 / 1903846153847) ∧
    -Real.log (500000000000 / 1903846153847) ≤ (1337023313 / 1000000000) := by
  have h := checkLog_sound (w := (903846153847 / 2903846153847)) (n := 12)
    (lo := (643876131 / 1000000000)) (hi := (160969033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1903846153847 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1903846153847 / 1000000000000) = 1/(500000000000 / 1903846153847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12943 : Bounds (1337023311 / 1000000000) (1337023313 / 1000000000) (Real.log (1903846153847 / 500000000000)) := by
  have h := reflection_log_12943_neg
  have he : Real.log (1903846153847 / 500000000000) = -Real.log (500000000000 / 1903846153847) := by
    rw [show ((1903846153847 / 500000000000) : ℝ) = ((500000000000 / 1903846153847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12944_neg : (461845441 / 1000000000) ≤ -Real.log (1000 / 1587) ∧
    -Real.log (1000 / 1587) ≤ (230922721 / 500000000) := by
  have h := checkLog_sound (w := (587 / 2587)) (n := 12)
    (lo := (461845441 / 1000000000)) (hi := (230922721 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1587 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1587 / 1000) = 1/(1000 / 1587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12944 : Bounds (461845441 / 1000000000) (230922721 / 500000000) (Real.log (1587 / 1000)) := by
  have h := reflection_log_12944_neg
  have he : Real.log (1587 / 1000) = -Real.log (1000 / 1587) := by
    rw [show ((1587 / 1000) : ℝ) = ((1000 / 1587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12945_neg : (176861537 / 200000000) ≤ -Real.log (413 / 1000) ∧
    -Real.log (413 / 1000) ≤ (884307687 / 1000000000) := by
  have h := checkLog_sound (w := (87 / 913)) (n := 12)
    (lo := (38232101 / 200000000)) (hi := (95580253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 413) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 413) = 1/(413 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12945 : Bounds (-884307687 / 1000000000) (-176861537 / 200000000) (Real.log (413 / 1000)) := by
  have h := reflection_log_12945_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12946_neg : (586827 / 1000000000) ≤ -Real.log (1000000 / 1000587) ∧
    -Real.log (1000000 / 1000587) ≤ (146707 / 250000000) := by
  have h := checkLog_sound (w := (587 / 2000587)) (n := 12)
    (lo := (586827 / 1000000000)) (hi := (146707 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000587 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000587 / 1000000) = 1/(1000000 / 1000587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12946 : Bounds (586827 / 1000000000) (146707 / 250000000) (Real.log (1000587 / 1000000)) := by
  have h := reflection_log_12946_neg
  have he : Real.log (1000587 / 1000000) = -Real.log (1000000 / 1000587) := by
    rw [show ((1000587 / 1000000) : ℝ) = ((1000000 / 1000587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12947_neg : (146793 / 250000000) ≤ -Real.log (999413 / 1000000) ∧
    -Real.log (999413 / 1000000) ≤ (587173 / 1000000000) := by
  have h := checkLog_sound (w := (587 / 1999413)) (n := 12)
    (lo := (146793 / 250000000)) (hi := (587173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999413) = 1/(999413 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12947 : Bounds (-587173 / 1000000000) (-146793 / 250000000) (Real.log (999413 / 1000000)) := by
  have h := reflection_log_12947_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12948_neg : (33925697 / 125000000) ≤ -Real.log (1000000 / 1311807) ∧
    -Real.log (1000000 / 1311807) ≤ (271405577 / 1000000000) := by
  have h := checkLog_sound (w := (311807 / 2311807)) (n := 12)
    (lo := (33925697 / 125000000)) (hi := (271405577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1311807 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1311807 / 1000000) = 1/(1000000 / 1311807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12948 : Bounds (33925697 / 125000000) (271405577 / 1000000000) (Real.log (1311807 / 1000000)) := by
  have h := reflection_log_12948_neg
  have he : Real.log (1311807 / 1000000) = -Real.log (1000000 / 1311807) := by
    rw [show ((1311807 / 1000000) : ℝ) = ((1000000 / 1311807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12949_neg : (373685957 / 1000000000) ≤ -Real.log (688193 / 1000000) ∧
    -Real.log (688193 / 1000000) ≤ (186842979 / 500000000) := by
  have h := checkLog_sound (w := (311807 / 1688193)) (n := 12)
    (lo := (373685957 / 1000000000)) (hi := (186842979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 688193) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 688193) = 1/(688193 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12949 : Bounds (-186842979 / 500000000) (-373685957 / 1000000000) (Real.log (688193 / 1000000)) := by
  have h := reflection_log_12949_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12950_neg : (136608731 / 500000000) ≤ -Real.log (500000 / 657093) ∧
    -Real.log (500000 / 657093) ≤ (273217463 / 1000000000) := by
  have h := checkLog_sound (w := (157093 / 1157093)) (n := 12)
    (lo := (136608731 / 500000000)) (hi := (273217463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((657093 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(657093 / 500000) = 1/(500000 / 657093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12950 : Bounds (136608731 / 500000000) (273217463 / 1000000000) (Real.log (657093 / 500000)) := by
  have h := reflection_log_12950_neg
  have he : Real.log (657093 / 500000) = -Real.log (500000 / 657093) := by
    rw [show ((657093 / 500000) : ℝ) = ((500000 / 657093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12951_neg : (15085953 / 40000000) ≤ -Real.log (342907 / 500000) ∧
    -Real.log (342907 / 500000) ≤ (188574413 / 500000000) := by
  have h := checkLog_sound (w := (157093 / 842907)) (n := 12)
    (lo := (15085953 / 40000000)) (hi := (188574413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 342907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 342907) = 1/(342907 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12951 : Bounds (-188574413 / 500000000) (-15085953 / 40000000) (Real.log (342907 / 500000)) := by
  have h := reflection_log_12951_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12952_neg : (51965681 / 500000000) ≤ -Real.log (225321789351 / 250000000000) ∧
    -Real.log (225321789351 / 250000000000) ≤ (103931363 / 1000000000) := by
  have h := checkLog_sound (w := (24678210649 / 475321789351)) (n := 12)
    (lo := (51965681 / 500000000)) (hi := (103931363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 225321789351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 225321789351) = 1/(225321789351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12952 : Bounds (-103931363 / 1000000000) (-51965681 / 500000000) (Real.log (225321789351 / 250000000000)) := by
  have h := reflection_log_12952_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12953_neg : (102280381 / 1000000000) ≤ -Real.log (902776394751 / 1000000000000) ∧
    -Real.log (902776394751 / 1000000000000) ≤ (51140191 / 500000000) := by
  have h := checkLog_sound (w := (97223605249 / 1902776394751)) (n := 12)
    (lo := (102280381 / 1000000000)) (hi := (51140191 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 902776394751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 902776394751) = 1/(902776394751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12953 : Bounds (-51140191 / 500000000) (-102280381 / 1000000000) (Real.log (902776394751 / 1000000000000)) := by
  have h := reflection_log_12953_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12954_neg : (645091533 / 1000000000) ≤ -Real.log (10000000000 / 19061614983) ∧
    -Real.log (10000000000 / 19061614983) ≤ (322545767 / 500000000) := by
  have h := checkLog_sound (w := (9061614983 / 29061614983)) (n := 12)
    (lo := (645091533 / 1000000000)) (hi := (322545767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19061614983 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19061614983 / 10000000000) = 1/(10000000000 / 19061614983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12954 : Bounds (645091533 / 1000000000) (322545767 / 500000000) (Real.log (19061614983 / 10000000000)) := by
  have h := reflection_log_12954_neg
  have he : Real.log (19061614983 / 10000000000) = -Real.log (10000000000 / 19061614983) := by
    rw [show ((19061614983 / 10000000000) : ℝ) = ((10000000000 / 19061614983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12955_neg : (650366287 / 1000000000) ≤ -Real.log (100000000000 / 191624259639) ∧
    -Real.log (100000000000 / 191624259639) ≤ (40647893 / 62500000) := by
  have h := checkLog_sound (w := (91624259639 / 291624259639)) (n := 12)
    (lo := (650366287 / 1000000000)) (hi := (40647893 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((191624259639 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(191624259639 / 100000000000) = 1/(100000000000 / 191624259639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12955 : Bounds (650366287 / 1000000000) (40647893 / 62500000) (Real.log (191624259639 / 100000000000)) := by
  have h := reflection_log_12955_neg
  have he : Real.log (191624259639 / 100000000000) = -Real.log (100000000000 / 191624259639) := by
    rw [show ((191624259639 / 100000000000) : ℝ) = ((100000000000 / 191624259639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12956_neg : (1337023311 / 1000000000) ≤ -Real.log (250000000000 / 951923076923) ∧
    -Real.log (250000000000 / 951923076923) ≤ (1337023313 / 1000000000) := by
  have h := checkLog_sound (w := (451923076923 / 1451923076923)) (n := 12)
    (lo := (643876131 / 1000000000)) (hi := (160969033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((951923076923 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(951923076923 / 500000000000) = 1/(250000000000 / 951923076923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12956 : Bounds (1337023311 / 1000000000) (1337023313 / 1000000000) (Real.log (951923076923 / 250000000000)) := by
  have h := reflection_log_12956_neg
  have he : Real.log (951923076923 / 250000000000) = -Real.log (250000000000 / 951923076923) := by
    rw [show ((951923076923 / 250000000000) : ℝ) = ((250000000000 / 951923076923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12957_neg : (1346153127 / 1000000000) ≤ -Real.log (250000000000 / 960653753027) ∧
    -Real.log (250000000000 / 960653753027) ≤ (1346153129 / 1000000000) := by
  have h := checkLog_sound (w := (460653753027 / 1460653753027)) (n := 12)
    (lo := (653005947 / 1000000000)) (hi := (163251487 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((960653753027 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(960653753027 / 500000000000) = 1/(250000000000 / 960653753027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12957 : Bounds (1346153127 / 1000000000) (1346153129 / 1000000000) (Real.log (960653753027 / 250000000000)) := by
  have h := reflection_log_12957_neg
  have he : Real.log (960653753027 / 250000000000) = -Real.log (250000000000 / 960653753027) := by
    rw [show ((960653753027 / 250000000000) : ℝ) = ((250000000000 / 960653753027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12958_neg : (1811461 / 3906250) ≤ -Real.log (100 / 159) ∧
    -Real.log (100 / 159) ≤ (463734017 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 259)) (n := 12)
    (lo := (1811461 / 3906250)) (hi := (463734017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159 / 100) = 1/(100 / 159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12958 : Bounds (1811461 / 3906250) (463734017 / 1000000000) (Real.log (159 / 100)) := by
  have h := reflection_log_12958_neg
  have he : Real.log (159 / 100) = -Real.log (100 / 159) := by
    rw [show ((159 / 100) : ℝ) = ((100 / 159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12959_neg : (445799059 / 500000000) ≤ -Real.log (41 / 100) ∧
    -Real.log (41 / 100) ≤ (22289953 / 25000000) := by
  have h := checkLog_sound (w := (9 / 91)) (n := 12)
    (lo := (99225469 / 500000000)) (hi := (198450939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 41) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50 / 41) = 1/(41 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12959 : Bounds (-22289953 / 25000000) (-445799059 / 500000000) (Real.log (41 / 100)) := by
  have h := reflection_log_12959_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12960_neg : (294913 / 500000000) ≤ -Real.log (100000 / 100059) ∧
    -Real.log (100000 / 100059) ≤ (589827 / 1000000000) := by
  have h := checkLog_sound (w := (59 / 200059)) (n := 12)
    (lo := (294913 / 500000000)) (hi := (589827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100059 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100059 / 100000) = 1/(100000 / 100059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12960 : Bounds (294913 / 500000000) (589827 / 1000000000) (Real.log (100059 / 100000)) := by
  have h := reflection_log_12960_neg
  have he : Real.log (100059 / 100000) = -Real.log (100000 / 100059) := by
    rw [show ((100059 / 100000) : ℝ) = ((100000 / 100059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12961_neg : (295087 / 500000000) ≤ -Real.log (99941 / 100000) ∧
    -Real.log (99941 / 100000) ≤ (23607 / 40000000) := by
  have h := checkLog_sound (w := (59 / 199941)) (n := 12)
    (lo := (295087 / 500000000)) (hi := (23607 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99941) = 1/(99941 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12961 : Bounds (-23607 / 40000000) (-295087 / 500000000) (Real.log (99941 / 100000)) := by
  have h := reflection_log_12961_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12962_neg : (272804193 / 1000000000) ≤ -Real.log (1000000 / 1313643) ∧
    -Real.log (1000000 / 1313643) ≤ (136402097 / 500000000) := by
  have h := checkLog_sound (w := (313643 / 2313643)) (n := 12)
    (lo := (272804193 / 1000000000)) (hi := (136402097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1313643 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1313643 / 1000000) = 1/(1000000 / 1313643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12962 : Bounds (272804193 / 1000000000) (136402097 / 500000000) (Real.log (1313643 / 1000000)) := by
  have h := reflection_log_12962_neg
  have he : Real.log (1313643 / 1000000) = -Real.log (1000000 / 1313643) := by
    rw [show ((1313643 / 1000000) : ℝ) = ((1000000 / 1313643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12963_neg : (188178689 / 500000000) ≤ -Real.log (686357 / 1000000) ∧
    -Real.log (686357 / 1000000) ≤ (376357379 / 1000000000) := by
  have h := checkLog_sound (w := (313643 / 1686357)) (n := 12)
    (lo := (188178689 / 500000000)) (hi := (376357379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 686357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 686357) = 1/(686357 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12963 : Bounds (-376357379 / 1000000000) (-188178689 / 500000000) (Real.log (686357 / 1000000)) := by
  have h := reflection_log_12963_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12964_neg : (274618869 / 1000000000) ≤ -Real.log (1000000 / 1316029) ∧
    -Real.log (1000000 / 1316029) ≤ (27461887 / 100000000) := by
  have h := checkLog_sound (w := (316029 / 2316029)) (n := 12)
    (lo := (274618869 / 1000000000)) (hi := (27461887 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1316029 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1316029 / 1000000) = 1/(1000000 / 1316029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12964 : Bounds (274618869 / 1000000000) (27461887 / 100000000) (Real.log (1316029 / 1000000)) := by
  have h := reflection_log_12964_neg
  have he : Real.log (1316029 / 1000000) = -Real.log (1000000 / 1316029) := by
    rw [show ((1316029 / 1000000) : ℝ) = ((1000000 / 1316029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12965_neg : (379839759 / 1000000000) ≤ -Real.log (683971 / 1000000) ∧
    -Real.log (683971 / 1000000) ≤ (4747997 / 12500000) := by
  have h := checkLog_sound (w := (316029 / 1683971)) (n := 12)
    (lo := (379839759 / 1000000000)) (hi := (4747997 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 683971) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 683971) = 1/(683971 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12965 : Bounds (-4747997 / 12500000) (-379839759 / 1000000000) (Real.log (683971 / 1000000)) := by
  have h := reflection_log_12965_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12966_neg : (10522089 / 100000000) ≤ -Real.log (900125671159 / 1000000000000) ∧
    -Real.log (900125671159 / 1000000000000) ≤ (105220891 / 1000000000) := by
  have h := checkLog_sound (w := (99874328841 / 1900125671159)) (n := 12)
    (lo := (10522089 / 100000000)) (hi := (105220891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 900125671159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 900125671159) = 1/(900125671159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12966 : Bounds (-105220891 / 1000000000) (-10522089 / 100000000) (Real.log (900125671159 / 1000000000000)) := by
  have h := reflection_log_12966_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12967_neg : (3236037 / 31250000) ≤ -Real.log (901628068551 / 1000000000000) ∧
    -Real.log (901628068551 / 1000000000000) ≤ (20710637 / 200000000) := by
  have h := checkLog_sound (w := (98371931449 / 1901628068551)) (n := 12)
    (lo := (3236037 / 31250000)) (hi := (20710637 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 901628068551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 901628068551) = 1/(901628068551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12967 : Bounds (-20710637 / 200000000) (-3236037 / 31250000) (Real.log (901628068551 / 1000000000000)) := by
  have h := reflection_log_12967_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12968_neg : (162290393 / 250000000) ≤ -Real.log (500000000000 / 956967729621) ∧
    -Real.log (500000000000 / 956967729621) ≤ (649161573 / 1000000000) := by
  have h := checkLog_sound (w := (456967729621 / 1456967729621)) (n := 12)
    (lo := (162290393 / 250000000)) (hi := (649161573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((956967729621 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(956967729621 / 500000000000) = 1/(500000000000 / 956967729621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12968 : Bounds (162290393 / 250000000) (649161573 / 1000000000) (Real.log (956967729621 / 500000000000)) := by
  have h := reflection_log_12968_neg
  have he : Real.log (956967729621 / 500000000000) = -Real.log (500000000000 / 956967729621) := by
    rw [show ((956967729621 / 500000000000) : ℝ) = ((500000000000 / 956967729621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12969_neg : (654458629 / 1000000000) ≤ -Real.log (250000000000 / 481025145803) ∧
    -Real.log (250000000000 / 481025145803) ≤ (65445863 / 100000000) := by
  have h := checkLog_sound (w := (231025145803 / 731025145803)) (n := 12)
    (lo := (654458629 / 1000000000)) (hi := (65445863 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((481025145803 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(481025145803 / 250000000000) = 1/(250000000000 / 481025145803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12969 : Bounds (654458629 / 1000000000) (65445863 / 100000000) (Real.log (481025145803 / 250000000000)) := by
  have h := reflection_log_12969_neg
  have he : Real.log (481025145803 / 250000000000) = -Real.log (250000000000 / 481025145803) := by
    rw [show ((481025145803 / 250000000000) : ℝ) = ((250000000000 / 481025145803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12970_neg : (1346153127 / 1000000000) ≤ -Real.log (500000000000 / 1921307506053) ∧
    -Real.log (500000000000 / 1921307506053) ≤ (1346153129 / 1000000000) := by
  have h := checkLog_sound (w := (921307506053 / 2921307506053)) (n := 12)
    (lo := (653005947 / 1000000000)) (hi := (163251487 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1921307506053 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1921307506053 / 1000000000000) = 1/(500000000000 / 1921307506053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12970 : Bounds (1346153127 / 1000000000) (1346153129 / 1000000000) (Real.log (1921307506053 / 500000000000)) := by
  have h := reflection_log_12970_neg
  have he : Real.log (1921307506053 / 500000000000) = -Real.log (500000000000 / 1921307506053) := by
    rw [show ((1921307506053 / 500000000000) : ℝ) = ((500000000000 / 1921307506053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12971_neg : (677666067 / 500000000) ≤ -Real.log (125000000000 / 484756097561) ∧
    -Real.log (125000000000 / 484756097561) ≤ (169416517 / 125000000) := by
  have h := checkLog_sound (w := (234756097561 / 734756097561)) (n := 12)
    (lo := (331092477 / 500000000)) (hi := (132436991 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((484756097561 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(484756097561 / 250000000000) = 1/(125000000000 / 484756097561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12971 : Bounds (677666067 / 500000000) (169416517 / 125000000) (Real.log (484756097561 / 125000000000)) := by
  have h := reflection_log_12971_neg
  have he : Real.log (484756097561 / 125000000000) = -Real.log (125000000000 / 484756097561) := by
    rw [show ((484756097561 / 125000000000) : ℝ) = ((125000000000 / 484756097561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12972_neg : (46561903 / 100000000) ≤ -Real.log (1000 / 1593) ∧
    -Real.log (1000 / 1593) ≤ (465619031 / 1000000000) := by
  have h := checkLog_sound (w := (593 / 2593)) (n := 12)
    (lo := (46561903 / 100000000)) (hi := (465619031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1593 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1593 / 1000) = 1/(1000 / 1593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12972 : Bounds (46561903 / 100000000) (465619031 / 1000000000) (Real.log (1593 / 1000)) := by
  have h := reflection_log_12972_neg
  have he : Real.log (1593 / 1000) = -Real.log (1000 / 1593) := by
    rw [show ((1593 / 1000) : ℝ) = ((1000 / 1593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12973_neg : (224735523 / 250000000) ≤ -Real.log (407 / 1000) ∧
    -Real.log (407 / 1000) ≤ (449471047 / 500000000) := by
  have h := checkLog_sound (w := (93 / 907)) (n := 12)
    (lo := (6431091 / 31250000)) (hi := (205794913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 407) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 407) = 1/(407 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12973 : Bounds (-449471047 / 500000000) (-224735523 / 250000000) (Real.log (407 / 1000)) := by
  have h := reflection_log_12973_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12974_neg : (74103 / 125000000) ≤ -Real.log (1000000 / 1000593) ∧
    -Real.log (1000000 / 1000593) ≤ (23713 / 40000000) := by
  have h := checkLog_sound (w := (593 / 2000593)) (n := 12)
    (lo := (74103 / 125000000)) (hi := (23713 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000593 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000593 / 1000000) = 1/(1000000 / 1000593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12974 : Bounds (74103 / 125000000) (23713 / 40000000) (Real.log (1000593 / 1000000)) := by
  have h := reflection_log_12974_neg
  have he : Real.log (1000593 / 1000000) = -Real.log (1000000 / 1000593) := by
    rw [show ((1000593 / 1000000) : ℝ) = ((1000000 / 1000593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12975_neg : (23727 / 40000000) ≤ -Real.log (999407 / 1000000) ∧
    -Real.log (999407 / 1000000) ≤ (74147 / 125000000) := by
  have h := checkLog_sound (w := (593 / 1999407)) (n := 12)
    (lo := (23727 / 40000000)) (hi := (74147 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999407) = 1/(999407 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12975 : Bounds (-74147 / 125000000) (-23727 / 40000000) (Real.log (999407 / 1000000)) := by
  have h := reflection_log_12975_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12976_neg : (137102329 / 500000000) ≤ -Real.log (250000 / 328871) ∧
    -Real.log (250000 / 328871) ≤ (274204659 / 1000000000) := by
  have h := checkLog_sound (w := (78871 / 578871)) (n := 12)
    (lo := (137102329 / 500000000)) (hi := (274204659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328871 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(328871 / 250000) = 1/(250000 / 328871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12976 : Bounds (137102329 / 500000000) (274204659 / 1000000000) (Real.log (328871 / 250000)) := by
  have h := reflection_log_12976_neg
  have he : Real.log (328871 / 250000) = -Real.log (250000 / 328871) := by
    rw [show ((328871 / 250000) : ℝ) = ((250000 / 328871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12977_neg : (379043259 / 1000000000) ≤ -Real.log (171129 / 250000) ∧
    -Real.log (171129 / 250000) ≤ (18952163 / 50000000) := by
  have h := checkLog_sound (w := (78871 / 421129)) (n := 12)
    (lo := (379043259 / 1000000000)) (hi := (18952163 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 171129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 171129) = 1/(171129 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12977 : Bounds (-18952163 / 50000000) (-379043259 / 1000000000) (Real.log (171129 / 250000)) := by
  have h := reflection_log_12977_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12978_neg : (276021349 / 1000000000) ≤ -Real.log (250000 / 329469) ∧
    -Real.log (250000 / 329469) ≤ (5520427 / 20000000) := by
  have h := checkLog_sound (w := (79469 / 579469)) (n := 12)
    (lo := (276021349 / 1000000000)) (hi := (5520427 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((329469 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(329469 / 250000) = 1/(250000 / 329469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12978 : Bounds (276021349 / 1000000000) (5520427 / 20000000) (Real.log (329469 / 250000)) := by
  have h := reflection_log_12978_neg
  have he : Real.log (329469 / 250000) = -Real.log (250000 / 329469) := by
    rw [show ((329469 / 250000) : ℝ) = ((250000 / 329469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12979_neg : (382543819 / 1000000000) ≤ -Real.log (170531 / 250000) ∧
    -Real.log (170531 / 250000) ≤ (19127191 / 50000000) := by
  have h := checkLog_sound (w := (79469 / 420531)) (n := 12)
    (lo := (382543819 / 1000000000)) (hi := (19127191 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 170531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 170531) = 1/(170531 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12979 : Bounds (-19127191 / 50000000) (-382543819 / 1000000000) (Real.log (170531 / 250000)) := by
  have h := reflection_log_12979_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12980_neg : (106522469 / 1000000000) ≤ -Real.log (56184678039 / 62500000000) ∧
    -Real.log (56184678039 / 62500000000) ≤ (10652247 / 100000000) := by
  have h := checkLog_sound (w := (6315321961 / 118684678039)) (n := 12)
    (lo := (106522469 / 1000000000)) (hi := (10652247 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 56184678039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 56184678039) = 1/(56184678039 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12980 : Bounds (-10652247 / 100000000) (-106522469 / 1000000000) (Real.log (56184678039 / 62500000000)) := by
  have h := reflection_log_12980_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12981_neg : (104838601 / 1000000000) ≤ -Real.log (56279365359 / 62500000000) ∧
    -Real.log (56279365359 / 62500000000) ≤ (52419301 / 500000000) := by
  have h := checkLog_sound (w := (6220634641 / 118779365359)) (n := 12)
    (lo := (104838601 / 1000000000)) (hi := (52419301 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 56279365359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 56279365359) = 1/(56279365359 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12981 : Bounds (-52419301 / 500000000) (-104838601 / 1000000000) (Real.log (56279365359 / 62500000000)) := by
  have h := reflection_log_12981_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12982_neg : (326623959 / 500000000) ≤ -Real.log (500000000000 / 960886232023) ∧
    -Real.log (500000000000 / 960886232023) ≤ (653247919 / 1000000000) := by
  have h := checkLog_sound (w := (460886232023 / 1460886232023)) (n := 12)
    (lo := (326623959 / 500000000)) (hi := (653247919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((960886232023 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(960886232023 / 500000000000) = 1/(500000000000 / 960886232023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12982 : Bounds (326623959 / 500000000) (653247919 / 1000000000) (Real.log (960886232023 / 500000000000)) := by
  have h := reflection_log_12982_neg
  have he : Real.log (960886232023 / 500000000000) = -Real.log (500000000000 / 960886232023) := by
    rw [show ((960886232023 / 500000000000) : ℝ) = ((500000000000 / 960886232023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12983_neg : (658565169 / 1000000000) ≤ -Real.log (500000000000 / 966009112713) ∧
    -Real.log (500000000000 / 966009112713) ≤ (65856517 / 100000000) := by
  have h := checkLog_sound (w := (466009112713 / 1466009112713)) (n := 12)
    (lo := (658565169 / 1000000000)) (hi := (65856517 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((966009112713 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(966009112713 / 500000000000) = 1/(500000000000 / 966009112713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12983 : Bounds (658565169 / 1000000000) (65856517 / 100000000) (Real.log (966009112713 / 500000000000)) := by
  have h := reflection_log_12983_neg
  have he : Real.log (966009112713 / 500000000000) = -Real.log (500000000000 / 966009112713) := by
    rw [show ((966009112713 / 500000000000) : ℝ) = ((500000000000 / 966009112713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12984_neg : (677666067 / 500000000) ≤ -Real.log (500000000000 / 1939024390243) ∧
    -Real.log (500000000000 / 1939024390243) ≤ (169416517 / 125000000) := by
  have h := checkLog_sound (w := (939024390243 / 2939024390243)) (n := 12)
    (lo := (331092477 / 500000000)) (hi := (132436991 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1939024390243 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1939024390243 / 1000000000000) = 1/(500000000000 / 1939024390243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12984 : Bounds (677666067 / 500000000) (169416517 / 125000000) (Real.log (1939024390243 / 500000000000)) := by
  have h := reflection_log_12984_neg
  have he : Real.log (1939024390243 / 500000000000) = -Real.log (500000000000 / 1939024390243) := by
    rw [show ((1939024390243 / 500000000000) : ℝ) = ((500000000000 / 1939024390243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12985_neg : (1364561123 / 1000000000) ≤ -Real.log (500000000000 / 1957002457003) ∧
    -Real.log (500000000000 / 1957002457003) ≤ (10916489 / 8000000) := by
  have h := checkLog_sound (w := (957002457003 / 2957002457003)) (n := 12)
    (lo := (671413943 / 1000000000)) (hi := (83926743 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1957002457003 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1957002457003 / 1000000000000) = 1/(500000000000 / 1957002457003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12985 : Bounds (1364561123 / 1000000000) (10916489 / 8000000) (Real.log (1957002457003 / 500000000000)) := by
  have h := reflection_log_12985_neg
  have he : Real.log (1957002457003 / 500000000000) = -Real.log (500000000000 / 1957002457003) := by
    rw [show ((1957002457003 / 500000000000) : ℝ) = ((500000000000 / 1957002457003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12986_neg : (467500499 / 1000000000) ≤ -Real.log (250 / 399) ∧
    -Real.log (250 / 399) ≤ (935001 / 2000000) := by
  have h := checkLog_sound (w := (149 / 649)) (n := 12)
    (lo := (467500499 / 1000000000)) (hi := (935001 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((399 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(399 / 250) = 1/(250 / 399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12986 : Bounds (467500499 / 1000000000) (935001 / 2000000) (Real.log (399 / 250)) := by
  have h := reflection_log_12986_neg
  have he : Real.log (399 / 250) = -Real.log (250 / 399) := by
    rw [show ((399 / 250) : ℝ) = ((250 / 399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12987_neg : (2265851 / 2500000) ≤ -Real.log (101 / 250) ∧
    -Real.log (101 / 250) ≤ (453170201 / 500000000) := by
  have h := checkLog_sound (w := (12 / 113)) (n := 12)
    (lo := (10659661 / 50000000)) (hi := (213193221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 101) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 101) = 1/(101 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12987 : Bounds (-453170201 / 500000000) (-2265851 / 2500000) (Real.log (101 / 250)) := by
  have h := reflection_log_12987_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12988_neg : (297911 / 500000000) ≤ -Real.log (250000 / 250149) ∧
    -Real.log (250000 / 250149) ≤ (595823 / 1000000000) := by
  have h := checkLog_sound (w := (149 / 500149)) (n := 12)
    (lo := (297911 / 500000000)) (hi := (595823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250149 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250149 / 250000) = 1/(250000 / 250149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12988 : Bounds (297911 / 500000000) (595823 / 1000000000) (Real.log (250149 / 250000)) := by
  have h := reflection_log_12988_neg
  have he : Real.log (250149 / 250000) = -Real.log (250000 / 250149) := by
    rw [show ((250149 / 250000) : ℝ) = ((250000 / 250149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12989_neg : (596177 / 1000000000) ≤ -Real.log (249851 / 250000) ∧
    -Real.log (249851 / 250000) ≤ (298089 / 500000000) := by
  have h := checkLog_sound (w := (149 / 499851)) (n := 12)
    (lo := (596177 / 1000000000)) (hi := (298089 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249851) = 1/(249851 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12989 : Bounds (-298089 / 500000000) (-596177 / 1000000000) (Real.log (249851 / 250000)) := by
  have h := reflection_log_12989_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12990_neg : (275606201 / 1000000000) ≤ -Real.log (1000000 / 1317329) ∧
    -Real.log (1000000 / 1317329) ≤ (137803101 / 500000000) := by
  have h := checkLog_sound (w := (317329 / 2317329)) (n := 12)
    (lo := (275606201 / 1000000000)) (hi := (137803101 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1317329 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1317329 / 1000000) = 1/(1000000 / 1317329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12990 : Bounds (275606201 / 1000000000) (137803101 / 500000000) (Real.log (1317329 / 1000000)) := by
  have h := reflection_log_12990_neg
  have he : Real.log (1317329 / 1000000) = -Real.log (1000000 / 1317329) := by
    rw [show ((1317329 / 1000000) : ℝ) = ((1000000 / 1317329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12991_neg : (381742233 / 1000000000) ≤ -Real.log (682671 / 1000000) ∧
    -Real.log (682671 / 1000000) ≤ (190871117 / 500000000) := by
  have h := checkLog_sound (w := (317329 / 1682671)) (n := 12)
    (lo := (381742233 / 1000000000)) (hi := (190871117 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 682671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 682671) = 1/(682671 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12991 : Bounds (-190871117 / 500000000) (-381742233 / 1000000000) (Real.log (682671 / 1000000)) := by
  have h := reflection_log_12991_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
