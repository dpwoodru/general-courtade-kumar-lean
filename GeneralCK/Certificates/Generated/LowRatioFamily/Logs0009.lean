import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_576_neg : (154411 / 1000000000) ≤ -Real.log (1249807 / 1250000) ∧
    -Real.log (1249807 / 1250000) ≤ (38603 / 250000000) := by
  have h := checkLog_sound (w := (193 / 2499807)) (n := 12)
    (lo := (154411 / 1000000000)) (hi := (38603 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249807) = 1/(1249807 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_576 : Bounds (-38603 / 250000000) (-154411 / 1000000000) (Real.log (1249807 / 1250000)) := by
  have h := reflection_log_576_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_577_neg : (745563 / 10000000) ≤ -Real.log (500000 / 538703) ∧
    -Real.log (500000 / 538703) ≤ (74556301 / 1000000000) := by
  have h := checkLog_sound (w := (38703 / 1038703)) (n := 12)
    (lo := (745563 / 10000000)) (hi := (74556301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538703 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538703 / 500000) = 1/(500000 / 538703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_577 : Bounds (745563 / 10000000) (74556301 / 1000000000) (Real.log (538703 / 500000)) := by
  have h := reflection_log_577_neg
  have he : Real.log (538703 / 500000) = -Real.log (500000 / 538703) := by
    rw [show ((538703 / 500000) : ℝ) = ((500000 / 538703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_578_neg : (80566011 / 1000000000) ≤ -Real.log (461297 / 500000) ∧
    -Real.log (461297 / 500000) ≤ (20141503 / 250000000) := by
  have h := checkLog_sound (w := (38703 / 961297)) (n := 12)
    (lo := (80566011 / 1000000000)) (hi := (20141503 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461297) = 1/(461297 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_578 : Bounds (-20141503 / 250000000) (-80566011 / 1000000000) (Real.log (461297 / 500000)) := by
  have h := reflection_log_578_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_579_neg : (74747481 / 1000000000) ≤ -Real.log (250000 / 269403) ∧
    -Real.log (250000 / 269403) ≤ (37373741 / 500000000) := by
  have h := checkLog_sound (w := (19403 / 519403)) (n := 12)
    (lo := (74747481 / 1000000000)) (hi := (37373741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269403 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269403 / 250000) = 1/(250000 / 269403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_579 : Bounds (74747481 / 1000000000) (37373741 / 500000000) (Real.log (269403 / 250000)) := by
  have h := reflection_log_579_neg
  have he : Real.log (269403 / 250000) = -Real.log (250000 / 269403) := by
    rw [show ((269403 / 250000) : ℝ) = ((250000 / 269403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_580_neg : (80789319 / 1000000000) ≤ -Real.log (230597 / 250000) ∧
    -Real.log (230597 / 250000) ≤ (2019733 / 25000000) := by
  have h := checkLog_sound (w := (19403 / 480597)) (n := 12)
    (lo := (80789319 / 1000000000)) (hi := (2019733 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230597) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230597) = 1/(230597 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_580 : Bounds (-2019733 / 25000000) (-80789319 / 1000000000) (Real.log (230597 / 250000)) := by
  have h := reflection_log_580_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_581_neg : (6041837 / 1000000000) ≤ -Real.log (62123523591 / 62500000000) ∧
    -Real.log (62123523591 / 62500000000) ≤ (3020919 / 500000000) := by
  have h := checkLog_sound (w := (376476409 / 124623523591)) (n := 12)
    (lo := (6041837 / 1000000000)) (hi := (3020919 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62123523591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62123523591) = 1/(62123523591 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_581 : Bounds (-3020919 / 500000000) (-6041837 / 1000000000) (Real.log (62123523591 / 62500000000)) := by
  have h := reflection_log_581_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_582_neg : (6009711 / 1000000000) ≤ -Real.log (248502077791 / 250000000000) ∧
    -Real.log (248502077791 / 250000000000) ≤ (375607 / 62500000) := by
  have h := checkLog_sound (w := (1497922209 / 498502077791)) (n := 12)
    (lo := (6009711 / 1000000000)) (hi := (375607 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248502077791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248502077791) = 1/(248502077791 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_582 : Bounds (-375607 / 62500000) (-6009711 / 1000000000) (Real.log (248502077791 / 250000000000)) := by
  have h := reflection_log_582_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_583_neg : (155122311 / 1000000000) ≤ -Real.log (500000000000 / 583900393889) ∧
    -Real.log (500000000000 / 583900393889) ≤ (19390289 / 125000000) := by
  have h := checkLog_sound (w := (83900393889 / 1083900393889)) (n := 12)
    (lo := (155122311 / 1000000000)) (hi := (19390289 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583900393889 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583900393889 / 500000000000) = 1/(500000000000 / 583900393889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_583 : Bounds (155122311 / 1000000000) (19390289 / 125000000) (Real.log (583900393889 / 500000000000)) := by
  have h := reflection_log_583_neg
  have he : Real.log (583900393889 / 500000000000) = -Real.log (500000000000 / 583900393889) := by
    rw [show ((583900393889 / 500000000000) : ℝ) = ((500000000000 / 583900393889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_584_neg : (155536801 / 1000000000) ≤ -Real.log (250000000000 / 292071232497) ∧
    -Real.log (250000000000 / 292071232497) ≤ (77768401 / 500000000) := by
  have h := checkLog_sound (w := (42071232497 / 542071232497)) (n := 12)
    (lo := (155536801 / 1000000000)) (hi := (77768401 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((292071232497 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(292071232497 / 250000000000) = 1/(250000000000 / 292071232497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_584 : Bounds (155536801 / 1000000000) (77768401 / 500000000) (Real.log (292071232497 / 250000000000)) := by
  have h := reflection_log_584_neg
  have he : Real.log (292071232497 / 250000000000) = -Real.log (250000000000 / 292071232497) := by
    rw [show ((292071232497 / 250000000000) : ℝ) = ((250000000000 / 292071232497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_585_neg : (311084691 / 1000000000) ≤ -Real.log (50000000000 / 68245240629) ∧
    -Real.log (50000000000 / 68245240629) ≤ (77771173 / 250000000) := by
  have h := checkLog_sound (w := (18245240629 / 118245240629)) (n := 12)
    (lo := (311084691 / 1000000000)) (hi := (77771173 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68245240629 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68245240629 / 50000000000) = 1/(50000000000 / 68245240629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_585 : Bounds (311084691 / 1000000000) (77771173 / 250000000) (Real.log (68245240629 / 50000000000)) := by
  have h := reflection_log_585_neg
  have he : Real.log (68245240629 / 50000000000) = -Real.log (50000000000 / 68245240629) := by
    rw [show ((68245240629 / 50000000000) : ℝ) = ((50000000000 / 68245240629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_586_neg : (77822393 / 250000000) ≤ -Real.log (100000000000 / 136518448439) ∧
    -Real.log (100000000000 / 136518448439) ≤ (311289573 / 1000000000) := by
  have h := checkLog_sound (w := (36518448439 / 236518448439)) (n := 12)
    (lo := (77822393 / 250000000)) (hi := (311289573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136518448439 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136518448439 / 100000000000) = 1/(100000000000 / 136518448439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_586 : Bounds (77822393 / 250000000) (311289573 / 1000000000) (Real.log (136518448439 / 100000000000)) := by
  have h := reflection_log_586_neg
  have he : Real.log (136518448439 / 100000000000) = -Real.log (100000000000 / 136518448439) := by
    rw [show ((136518448439 / 100000000000) : ℝ) = ((100000000000 / 136518448439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_587_neg : (143667349 / 1000000000) ≤ -Real.log (2000 / 2309) ∧
    -Real.log (2000 / 2309) ≤ (2873347 / 20000000) := by
  have h := checkLog_sound (w := (309 / 4309)) (n := 12)
    (lo := (143667349 / 1000000000)) (hi := (2873347 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2309 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2309 / 2000) = 1/(2000 / 2309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_587 : Bounds (143667349 / 1000000000) (2873347 / 20000000) (Real.log (2309 / 2000)) := by
  have h := reflection_log_587_neg
  have he : Real.log (2309 / 2000) = -Real.log (2000 / 2309) := by
    rw [show ((2309 / 2000) : ℝ) = ((2000 / 2309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_588_neg : (16782711 / 100000000) ≤ -Real.log (1691 / 2000) ∧
    -Real.log (1691 / 2000) ≤ (167827111 / 1000000000) := by
  have h := checkLog_sound (w := (309 / 3691)) (n := 12)
    (lo := (16782711 / 100000000)) (hi := (167827111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1691) = 1/(1691 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_588 : Bounds (-167827111 / 1000000000) (-16782711 / 100000000) (Real.log (1691 / 2000)) := by
  have h := reflection_log_588_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_589_neg : (19311 / 125000000) ≤ -Real.log (2000000 / 2000309) ∧
    -Real.log (2000000 / 2000309) ≤ (154489 / 1000000000) := by
  have h := checkLog_sound (w := (309 / 4000309)) (n := 12)
    (lo := (19311 / 125000000)) (hi := (154489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000309 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000309 / 2000000) = 1/(2000000 / 2000309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_589 : Bounds (19311 / 125000000) (154489 / 1000000000) (Real.log (2000309 / 2000000)) := by
  have h := reflection_log_589_neg
  have he : Real.log (2000309 / 2000000) = -Real.log (2000000 / 2000309) := by
    rw [show ((2000309 / 2000000) : ℝ) = ((2000000 / 2000309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_590_neg : (154511 / 1000000000) ≤ -Real.log (1999691 / 2000000) ∧
    -Real.log (1999691 / 2000000) ≤ (9657 / 62500000) := by
  have h := checkLog_sound (w := (309 / 3999691)) (n := 12)
    (lo := (154511 / 1000000000)) (hi := (9657 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999691) = 1/(1999691 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_590 : Bounds (-9657 / 62500000) (-154511 / 1000000000) (Real.log (1999691 / 2000000)) := by
  have h := reflection_log_590_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_591_neg : (14920727 / 200000000) ≤ -Real.log (1000000 / 1077457) ∧
    -Real.log (1000000 / 1077457) ≤ (18650909 / 250000000) := by
  have h := checkLog_sound (w := (77457 / 2077457)) (n := 12)
    (lo := (14920727 / 200000000)) (hi := (18650909 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077457 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077457 / 1000000) = 1/(1000000 / 1077457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_591 : Bounds (14920727 / 200000000) (18650909 / 250000000) (Real.log (1077457 / 1000000)) := by
  have h := reflection_log_591_neg
  have he : Real.log (1077457 / 1000000) = -Real.log (1000000 / 1077457) := by
    rw [show ((1077457 / 1000000) : ℝ) = ((1000000 / 1077457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_592_neg : (80621291 / 1000000000) ≤ -Real.log (922543 / 1000000) ∧
    -Real.log (922543 / 1000000) ≤ (20155323 / 250000000) := by
  have h := checkLog_sound (w := (77457 / 1922543)) (n := 12)
    (lo := (80621291 / 1000000000)) (hi := (20155323 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922543) = 1/(922543 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_592 : Bounds (-20155323 / 250000000) (-80621291 / 1000000000) (Real.log (922543 / 1000000)) := by
  have h := reflection_log_592_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_593_neg : (74793879 / 1000000000) ≤ -Real.log (500000 / 538831) ∧
    -Real.log (500000 / 538831) ≤ (1869847 / 25000000) := by
  have h := checkLog_sound (w := (38831 / 1038831)) (n := 12)
    (lo := (74793879 / 1000000000)) (hi := (1869847 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538831 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538831 / 500000) = 1/(500000 / 538831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_593 : Bounds (74793879 / 1000000000) (1869847 / 25000000) (Real.log (538831 / 500000)) := by
  have h := reflection_log_593_neg
  have he : Real.log (538831 / 500000) = -Real.log (500000 / 538831) := by
    rw [show ((538831 / 500000) : ℝ) = ((500000 / 538831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_594_neg : (10105441 / 125000000) ≤ -Real.log (461169 / 500000) ∧
    -Real.log (461169 / 500000) ≤ (80843529 / 1000000000) := by
  have h := checkLog_sound (w := (38831 / 961169)) (n := 12)
    (lo := (10105441 / 125000000)) (hi := (80843529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461169) = 1/(461169 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_594 : Bounds (-80843529 / 1000000000) (-10105441 / 125000000) (Real.log (461169 / 500000)) := by
  have h := reflection_log_594_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_595_neg : (378103 / 62500000) ≤ -Real.log (248492153439 / 250000000000) ∧
    -Real.log (248492153439 / 250000000000) ≤ (6049649 / 1000000000) := by
  have h := checkLog_sound (w := (1507846561 / 498492153439)) (n := 12)
    (lo := (378103 / 62500000)) (hi := (6049649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248492153439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248492153439) = 1/(248492153439 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_595 : Bounds (-6049649 / 1000000000) (-378103 / 62500000) (Real.log (248492153439 / 250000000000)) := by
  have h := reflection_log_595_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_596_neg : (752207 / 125000000) ≤ -Real.log (994000413151 / 1000000000000) ∧
    -Real.log (994000413151 / 1000000000000) ≤ (6017657 / 1000000000) := by
  have h := checkLog_sound (w := (5999586849 / 1994000413151)) (n := 12)
    (lo := (752207 / 125000000)) (hi := (6017657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 994000413151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 994000413151) = 1/(994000413151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_596 : Bounds (-6017657 / 1000000000) (-752207 / 125000000) (Real.log (994000413151 / 1000000000000)) := by
  have h := reflection_log_596_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_597_neg : (77612463 / 500000000) ≤ -Real.log (125000000000 / 145990078511) ∧
    -Real.log (125000000000 / 145990078511) ≤ (155224927 / 1000000000) := by
  have h := checkLog_sound (w := (20990078511 / 270990078511)) (n := 12)
    (lo := (77612463 / 500000000)) (hi := (155224927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145990078511 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145990078511 / 125000000000) = 1/(125000000000 / 145990078511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_597 : Bounds (77612463 / 500000000) (155224927 / 1000000000) (Real.log (145990078511 / 125000000000)) := by
  have h := reflection_log_597_neg
  have he : Real.log (145990078511 / 125000000000) = -Real.log (125000000000 / 145990078511) := by
    rw [show ((145990078511 / 125000000000) : ℝ) = ((125000000000 / 145990078511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_598_neg : (155637407 / 1000000000) ≤ -Real.log (62500000000 / 73025154553) ∧
    -Real.log (62500000000 / 73025154553) ≤ (4863669 / 31250000) := by
  have h := checkLog_sound (w := (10525154553 / 135525154553)) (n := 12)
    (lo := (155637407 / 1000000000)) (hi := (4863669 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73025154553 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73025154553 / 62500000000) = 1/(62500000000 / 73025154553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_598 : Bounds (155637407 / 1000000000) (4863669 / 31250000) (Real.log (73025154553 / 62500000000)) := by
  have h := reflection_log_598_neg
  have he : Real.log (73025154553 / 62500000000) = -Real.log (62500000000 / 73025154553) := by
    rw [show ((73025154553 / 62500000000) : ℝ) = ((62500000000 / 73025154553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_599_neg : (77822393 / 250000000) ≤ -Real.log (250000000000 / 341296121097) ∧
    -Real.log (250000000000 / 341296121097) ≤ (311289573 / 1000000000) := by
  have h := checkLog_sound (w := (91296121097 / 591296121097)) (n := 12)
    (lo := (77822393 / 250000000)) (hi := (311289573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((341296121097 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(341296121097 / 250000000000) = 1/(250000000000 / 341296121097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_599 : Bounds (77822393 / 250000000) (311289573 / 1000000000) (Real.log (341296121097 / 250000000000)) := by
  have h := reflection_log_599_neg
  have he : Real.log (341296121097 / 250000000000) = -Real.log (250000000000 / 341296121097) := by
    rw [show ((341296121097 / 250000000000) : ℝ) = ((250000000000 / 341296121097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_600_neg : (15574723 / 50000000) ≤ -Real.log (500000000000 / 682732111177) ∧
    -Real.log (500000000000 / 682732111177) ≤ (311494461 / 1000000000) := by
  have h := checkLog_sound (w := (182732111177 / 1182732111177)) (n := 12)
    (lo := (15574723 / 50000000)) (hi := (311494461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((682732111177 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(682732111177 / 500000000000) = 1/(500000000000 / 682732111177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_600 : Bounds (15574723 / 50000000) (311494461 / 1000000000) (Real.log (682732111177 / 500000000000)) := by
  have h := reflection_log_600_neg
  have he : Real.log (682732111177 / 500000000000) = -Real.log (500000000000 / 682732111177) := by
    rw [show ((682732111177 / 500000000000) : ℝ) = ((500000000000 / 682732111177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_601_neg : (143753963 / 1000000000) ≤ -Real.log (5000 / 5773) ∧
    -Real.log (5000 / 5773) ≤ (35938491 / 250000000) := by
  have h := checkLog_sound (w := (773 / 10773)) (n := 12)
    (lo := (143753963 / 1000000000)) (hi := (35938491 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5773 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5773 / 5000) = 1/(5000 / 5773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_601 : Bounds (143753963 / 1000000000) (35938491 / 250000000) (Real.log (5773 / 5000)) := by
  have h := reflection_log_601_neg
  have he : Real.log (5773 / 5000) = -Real.log (5000 / 5773) := by
    rw [show ((5773 / 5000) : ℝ) = ((5000 / 5773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_602_neg : (16794539 / 100000000) ≤ -Real.log (4227 / 5000) ∧
    -Real.log (4227 / 5000) ≤ (167945391 / 1000000000) := by
  have h := checkLog_sound (w := (773 / 9227)) (n := 12)
    (lo := (16794539 / 100000000)) (hi := (167945391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4227) = 1/(4227 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_602 : Bounds (-167945391 / 1000000000) (-16794539 / 100000000) (Real.log (4227 / 5000)) := by
  have h := reflection_log_602_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_603_neg : (38647 / 250000000) ≤ -Real.log (5000000 / 5000773) ∧
    -Real.log (5000000 / 5000773) ≤ (154589 / 1000000000) := by
  have h := checkLog_sound (w := (773 / 10000773)) (n := 12)
    (lo := (38647 / 250000000)) (hi := (154589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000773 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000773 / 5000000) = 1/(5000000 / 5000773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_603 : Bounds (38647 / 250000000) (154589 / 1000000000) (Real.log (5000773 / 5000000)) := by
  have h := reflection_log_603_neg
  have he : Real.log (5000773 / 5000000) = -Real.log (5000000 / 5000773) := by
    rw [show ((5000773 / 5000000) : ℝ) = ((5000000 / 5000773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_604_neg : (154611 / 1000000000) ≤ -Real.log (4999227 / 5000000) ∧
    -Real.log (4999227 / 5000000) ≤ (38653 / 250000000) := by
  have h := checkLog_sound (w := (773 / 9999227)) (n := 12)
    (lo := (154611 / 1000000000)) (hi := (38653 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999227) = 1/(4999227 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_604 : Bounds (-38653 / 250000000) (-154611 / 1000000000) (Real.log (4999227 / 5000000)) := by
  have h := reflection_log_604_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_605_neg : (74650039 / 1000000000) ≤ -Real.log (1000000 / 1077507) ∧
    -Real.log (1000000 / 1077507) ≤ (1866251 / 25000000) := by
  have h := checkLog_sound (w := (77507 / 2077507)) (n := 12)
    (lo := (74650039 / 1000000000)) (hi := (1866251 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077507 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077507 / 1000000) = 1/(1000000 / 1077507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_605 : Bounds (74650039 / 1000000000) (1866251 / 25000000) (Real.log (1077507 / 1000000)) := by
  have h := reflection_log_605_neg
  have he : Real.log (1077507 / 1000000) = -Real.log (1000000 / 1077507) := by
    rw [show ((1077507 / 1000000) : ℝ) = ((1000000 / 1077507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_606_neg : (80675491 / 1000000000) ≤ -Real.log (922493 / 1000000) ∧
    -Real.log (922493 / 1000000) ≤ (20168873 / 250000000) := by
  have h := checkLog_sound (w := (77507 / 1922493)) (n := 12)
    (lo := (80675491 / 1000000000)) (hi := (20168873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922493) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922493) = 1/(922493 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_606 : Bounds (-20168873 / 250000000) (-80675491 / 1000000000) (Real.log (922493 / 1000000)) := by
  have h := reflection_log_606_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_607_neg : (74841203 / 1000000000) ≤ -Real.log (1000000 / 1077713) ∧
    -Real.log (1000000 / 1077713) ≤ (18710301 / 250000000) := by
  have h := checkLog_sound (w := (77713 / 2077713)) (n := 12)
    (lo := (74841203 / 1000000000)) (hi := (18710301 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077713 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077713 / 1000000) = 1/(1000000 / 1077713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_607 : Bounds (74841203 / 1000000000) (18710301 / 250000000) (Real.log (1077713 / 1000000)) := by
  have h := reflection_log_607_neg
  have he : Real.log (1077713 / 1000000) = -Real.log (1000000 / 1077713) := by
    rw [show ((1077713 / 1000000) : ℝ) = ((1000000 / 1077713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_608_neg : (10112353 / 125000000) ≤ -Real.log (922287 / 1000000) ∧
    -Real.log (922287 / 1000000) ≤ (3235953 / 40000000) := by
  have h := checkLog_sound (w := (77713 / 1922287)) (n := 12)
    (lo := (10112353 / 125000000)) (hi := (3235953 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922287) = 1/(922287 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_608 : Bounds (-3235953 / 40000000) (-10112353 / 125000000) (Real.log (922287 / 1000000)) := by
  have h := reflection_log_608_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_609_neg : (302881 / 50000000) ≤ -Real.log (993960689631 / 1000000000000) ∧
    -Real.log (993960689631 / 1000000000000) ≤ (6057621 / 1000000000) := by
  have h := checkLog_sound (w := (6039310369 / 1993960689631)) (n := 12)
    (lo := (302881 / 50000000)) (hi := (6057621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993960689631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993960689631) = 1/(993960689631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_609 : Bounds (-6057621 / 1000000000) (-302881 / 50000000) (Real.log (993960689631 / 1000000000000)) := by
  have h := reflection_log_609_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_610_neg : (6025451 / 1000000000) ≤ -Real.log (993992664951 / 1000000000000) ∧
    -Real.log (993992664951 / 1000000000000) ≤ (1506363 / 250000000) := by
  have h := checkLog_sound (w := (6007335049 / 1993992664951)) (n := 12)
    (lo := (6025451 / 1000000000)) (hi := (1506363 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993992664951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993992664951) = 1/(993992664951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_610 : Bounds (-1506363 / 250000000) (-6025451 / 1000000000) (Real.log (993992664951 / 1000000000000)) := by
  have h := reflection_log_610_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_611_neg : (15532553 / 100000000) ≤ -Real.log (500000000000 / 584019065727) ∧
    -Real.log (500000000000 / 584019065727) ≤ (155325531 / 1000000000) := by
  have h := checkLog_sound (w := (84019065727 / 1084019065727)) (n := 12)
    (lo := (15532553 / 100000000)) (hi := (155325531 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584019065727 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584019065727 / 500000000000) = 1/(500000000000 / 584019065727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_611 : Bounds (15532553 / 100000000) (155325531 / 1000000000) (Real.log (584019065727 / 500000000000)) := by
  have h := reflection_log_611_neg
  have he : Real.log (584019065727 / 500000000000) = -Real.log (500000000000 / 584019065727) := by
    rw [show ((584019065727 / 500000000000) : ℝ) = ((500000000000 / 584019065727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_612_neg : (155740027 / 1000000000) ≤ -Real.log (500000000000 / 584261189847) ∧
    -Real.log (500000000000 / 584261189847) ≤ (38935007 / 250000000) := by
  have h := checkLog_sound (w := (84261189847 / 1084261189847)) (n := 12)
    (lo := (155740027 / 1000000000)) (hi := (38935007 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584261189847 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584261189847 / 500000000000) = 1/(500000000000 / 584261189847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_612 : Bounds (155740027 / 1000000000) (38935007 / 250000000) (Real.log (584261189847 / 500000000000)) := by
  have h := reflection_log_612_neg
  have he : Real.log (584261189847 / 500000000000) = -Real.log (500000000000 / 584261189847) := by
    rw [show ((584261189847 / 500000000000) : ℝ) = ((500000000000 / 584261189847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_613_neg : (15574723 / 50000000) ≤ -Real.log (62500000000 / 85341513897) ∧
    -Real.log (62500000000 / 85341513897) ≤ (311494461 / 1000000000) := by
  have h := checkLog_sound (w := (22841513897 / 147841513897)) (n := 12)
    (lo := (15574723 / 50000000)) (hi := (311494461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((85341513897 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(85341513897 / 62500000000) = 1/(62500000000 / 85341513897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_613 : Bounds (15574723 / 50000000) (311494461 / 1000000000) (Real.log (85341513897 / 62500000000)) := by
  have h := reflection_log_613_neg
  have he : Real.log (85341513897 / 62500000000) = -Real.log (62500000000 / 85341513897) := by
    rw [show ((85341513897 / 62500000000) : ℝ) = ((62500000000 / 85341513897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_614_neg : (155849677 / 500000000) ≤ -Real.log (500000000000 / 682872013249) ∧
    -Real.log (500000000000 / 682872013249) ≤ (62339871 / 200000000) := by
  have h := checkLog_sound (w := (182872013249 / 1182872013249)) (n := 12)
    (lo := (155849677 / 500000000)) (hi := (62339871 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((682872013249 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(682872013249 / 500000000000) = 1/(500000000000 / 682872013249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_614 : Bounds (155849677 / 500000000) (62339871 / 200000000) (Real.log (682872013249 / 500000000000)) := by
  have h := reflection_log_614_neg
  have he : Real.log (682872013249 / 500000000000) = -Real.log (500000000000 / 682872013249) := by
    rw [show ((682872013249 / 500000000000) : ℝ) = ((500000000000 / 682872013249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_615_neg : (143840569 / 1000000000) ≤ -Real.log (10000 / 11547) ∧
    -Real.log (10000 / 11547) ≤ (14384057 / 100000000) := by
  have h := checkLog_sound (w := (1547 / 21547)) (n := 12)
    (lo := (143840569 / 1000000000)) (hi := (14384057 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11547 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11547 / 10000) = 1/(10000 / 11547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_615 : Bounds (143840569 / 1000000000) (14384057 / 100000000) (Real.log (11547 / 10000)) := by
  have h := reflection_log_615_neg
  have he : Real.log (11547 / 10000) = -Real.log (10000 / 11547) := by
    rw [show ((11547 / 10000) : ℝ) = ((10000 / 11547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_616_neg : (33612737 / 200000000) ≤ -Real.log (8453 / 10000) ∧
    -Real.log (8453 / 10000) ≤ (84031843 / 500000000) := by
  have h := checkLog_sound (w := (1547 / 18453)) (n := 12)
    (lo := (33612737 / 200000000)) (hi := (84031843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8453) = 1/(8453 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_616 : Bounds (-84031843 / 500000000) (-33612737 / 200000000) (Real.log (8453 / 10000)) := by
  have h := reflection_log_616_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_617_neg : (2417 / 15625000) ≤ -Real.log (10000000 / 10001547) ∧
    -Real.log (10000000 / 10001547) ≤ (154689 / 1000000000) := by
  have h := checkLog_sound (w := (1547 / 20001547)) (n := 12)
    (lo := (2417 / 15625000)) (hi := (154689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001547 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001547 / 10000000) = 1/(10000000 / 10001547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_617 : Bounds (2417 / 15625000) (154689 / 1000000000) (Real.log (10001547 / 10000000)) := by
  have h := reflection_log_617_neg
  have he : Real.log (10001547 / 10000000) = -Real.log (10000000 / 10001547) := by
    rw [show ((10001547 / 10000000) : ℝ) = ((10000000 / 10001547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_618_neg : (154711 / 1000000000) ≤ -Real.log (9998453 / 10000000) ∧
    -Real.log (9998453 / 10000000) ≤ (19339 / 125000000) := by
  have h := checkLog_sound (w := (1547 / 19998453)) (n := 12)
    (lo := (154711 / 1000000000)) (hi := (19339 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998453) = 1/(9998453 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_618 : Bounds (-19339 / 125000000) (-154711 / 1000000000) (Real.log (9998453 / 10000000)) := by
  have h := reflection_log_618_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_619_neg : (74697369 / 1000000000) ≤ -Real.log (500000 / 538779) ∧
    -Real.log (500000 / 538779) ≤ (7469737 / 100000000) := by
  have h := checkLog_sound (w := (38779 / 1038779)) (n := 12)
    (lo := (74697369 / 1000000000)) (hi := (7469737 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538779 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538779 / 500000) = 1/(500000 / 538779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_619 : Bounds (74697369 / 1000000000) (7469737 / 100000000) (Real.log (538779 / 500000)) := by
  have h := reflection_log_619_neg
  have he : Real.log (538779 / 500000) = -Real.log (500000 / 538779) := by
    rw [show ((538779 / 500000) : ℝ) = ((500000 / 538779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_620_neg : (80730777 / 1000000000) ≤ -Real.log (461221 / 500000) ∧
    -Real.log (461221 / 500000) ≤ (40365389 / 500000000) := by
  have h := checkLog_sound (w := (38779 / 961221)) (n := 12)
    (lo := (80730777 / 1000000000)) (hi := (40365389 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461221) = 1/(461221 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_620 : Bounds (-40365389 / 500000000) (-80730777 / 1000000000) (Real.log (461221 / 500000)) := by
  have h := reflection_log_620_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_621_neg : (18722131 / 250000000) ≤ -Real.log (250000 / 269441) ∧
    -Real.log (250000 / 269441) ≤ (2995541 / 40000000) := by
  have h := checkLog_sound (w := (19441 / 519441)) (n := 12)
    (lo := (18722131 / 250000000)) (hi := (2995541 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269441 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269441 / 250000) = 1/(250000 / 269441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_621 : Bounds (18722131 / 250000000) (2995541 / 40000000) (Real.log (269441 / 250000)) := by
  have h := reflection_log_621_neg
  have he : Real.log (269441 / 250000) = -Real.log (250000 / 269441) := by
    rw [show ((269441 / 250000) : ℝ) = ((250000 / 269441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_622_neg : (40477061 / 500000000) ≤ -Real.log (230559 / 250000) ∧
    -Real.log (230559 / 250000) ≤ (80954123 / 1000000000) := by
  have h := checkLog_sound (w := (19441 / 480559)) (n := 12)
    (lo := (40477061 / 500000000)) (hi := (80954123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230559) = 1/(230559 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_622 : Bounds (-80954123 / 1000000000) (-40477061 / 500000000) (Real.log (230559 / 250000)) := by
  have h := reflection_log_622_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_623_neg : (3032799 / 500000000) ≤ -Real.log (62122047519 / 62500000000) ∧
    -Real.log (62122047519 / 62500000000) ≤ (6065599 / 1000000000) := by
  have h := checkLog_sound (w := (377952481 / 124622047519)) (n := 12)
    (lo := (3032799 / 500000000)) (hi := (6065599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62122047519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62122047519) = 1/(62122047519 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_623 : Bounds (-6065599 / 1000000000) (-3032799 / 500000000) (Real.log (62122047519 / 62500000000)) := by
  have h := reflection_log_623_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_624_neg : (6033407 / 1000000000) ≤ -Real.log (248496189159 / 250000000000) ∧
    -Real.log (248496189159 / 250000000000) ≤ (11784 / 1953125) := by
  have h := checkLog_sound (w := (1503810841 / 498496189159)) (n := 12)
    (lo := (6033407 / 1000000000)) (hi := (11784 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248496189159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248496189159) = 1/(248496189159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_624 : Bounds (-11784 / 1953125) (-6033407 / 1000000000) (Real.log (248496189159 / 250000000000)) := by
  have h := reflection_log_624_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_625_neg : (155428147 / 1000000000) ≤ -Real.log (125000000000 / 146019749751) ∧
    -Real.log (125000000000 / 146019749751) ≤ (38857037 / 250000000) := by
  have h := checkLog_sound (w := (21019749751 / 271019749751)) (n := 12)
    (lo := (155428147 / 1000000000)) (hi := (38857037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146019749751 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146019749751 / 125000000000) = 1/(125000000000 / 146019749751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_625 : Bounds (155428147 / 1000000000) (38857037 / 250000000) (Real.log (146019749751 / 125000000000)) := by
  have h := reflection_log_625_neg
  have he : Real.log (146019749751 / 125000000000) = -Real.log (125000000000 / 146019749751) := by
    rw [show ((146019749751 / 125000000000) : ℝ) = ((125000000000 / 146019749751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_626_neg : (155842647 / 1000000000) ≤ -Real.log (500000000000 / 584321149901) ∧
    -Real.log (500000000000 / 584321149901) ≤ (19480331 / 125000000) := by
  have h := checkLog_sound (w := (84321149901 / 1084321149901)) (n := 12)
    (lo := (155842647 / 1000000000)) (hi := (19480331 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584321149901 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584321149901 / 500000000000) = 1/(500000000000 / 584321149901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_626 : Bounds (155842647 / 1000000000) (19480331 / 125000000) (Real.log (584321149901 / 500000000000)) := by
  have h := reflection_log_626_neg
  have he : Real.log (584321149901 / 500000000000) = -Real.log (500000000000 / 584321149901) := by
    rw [show ((584321149901 / 500000000000) : ℝ) = ((500000000000 / 584321149901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_627_neg : (155849677 / 500000000) ≤ -Real.log (7812500000 / 10669875207) ∧
    -Real.log (7812500000 / 10669875207) ≤ (62339871 / 200000000) := by
  have h := checkLog_sound (w := (2857375207 / 18482375207)) (n := 12)
    (lo := (155849677 / 500000000)) (hi := (62339871 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10669875207 / 7812500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10669875207 / 7812500000) = 1/(7812500000 / 10669875207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_627 : Bounds (155849677 / 500000000) (62339871 / 200000000) (Real.log (10669875207 / 7812500000)) := by
  have h := reflection_log_627_neg
  have he : Real.log (10669875207 / 7812500000) = -Real.log (7812500000 / 10669875207) := by
    rw [show ((10669875207 / 7812500000) : ℝ) = ((7812500000 / 10669875207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_628_neg : (62380851 / 200000000) ≤ -Real.log (500000000000 / 683011948421) ∧
    -Real.log (500000000000 / 683011948421) ≤ (609188 / 1953125) := by
  have h := checkLog_sound (w := (183011948421 / 1183011948421)) (n := 12)
    (lo := (62380851 / 200000000)) (hi := (609188 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683011948421 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683011948421 / 500000000000) = 1/(500000000000 / 683011948421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_628 : Bounds (62380851 / 200000000) (609188 / 1953125) (Real.log (683011948421 / 500000000000)) := by
  have h := reflection_log_628_neg
  have he : Real.log (683011948421 / 500000000000) = -Real.log (500000000000 / 683011948421) := by
    rw [show ((683011948421 / 500000000000) : ℝ) = ((500000000000 / 683011948421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_629_neg : (1124431 / 7812500) ≤ -Real.log (2500 / 2887) ∧
    -Real.log (2500 / 2887) ≤ (143927169 / 1000000000) := by
  have h := checkLog_sound (w := (387 / 5387)) (n := 12)
    (lo := (1124431 / 7812500)) (hi := (143927169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2887 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2887 / 2500) = 1/(2500 / 2887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_629 : Bounds (1124431 / 7812500) (143927169 / 1000000000) (Real.log (2887 / 2500)) := by
  have h := reflection_log_629_neg
  have he : Real.log (2887 / 2500) = -Real.log (2500 / 2887) := by
    rw [show ((2887 / 2500) : ℝ) = ((2500 / 2887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_630_neg : (168181993 / 1000000000) ≤ -Real.log (2113 / 2500) ∧
    -Real.log (2113 / 2500) ≤ (84090997 / 500000000) := by
  have h := checkLog_sound (w := (387 / 4613)) (n := 12)
    (lo := (168181993 / 1000000000)) (hi := (84090997 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2113) = 1/(2113 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_630 : Bounds (-84090997 / 500000000) (-168181993 / 1000000000) (Real.log (2113 / 2500)) := by
  have h := reflection_log_630_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_631_neg : (38697 / 250000000) ≤ -Real.log (2500000 / 2500387) ∧
    -Real.log (2500000 / 2500387) ≤ (154789 / 1000000000) := by
  have h := checkLog_sound (w := (387 / 5000387)) (n := 12)
    (lo := (38697 / 250000000)) (hi := (154789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500387 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500387 / 2500000) = 1/(2500000 / 2500387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_631 : Bounds (38697 / 250000000) (154789 / 1000000000) (Real.log (2500387 / 2500000)) := by
  have h := reflection_log_631_neg
  have he : Real.log (2500387 / 2500000) = -Real.log (2500000 / 2500387) := by
    rw [show ((2500387 / 2500000) : ℝ) = ((2500000 / 2500387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_632_neg : (154811 / 1000000000) ≤ -Real.log (2499613 / 2500000) ∧
    -Real.log (2499613 / 2500000) ≤ (38703 / 250000000) := by
  have h := checkLog_sound (w := (387 / 4999613)) (n := 12)
    (lo := (154811 / 1000000000)) (hi := (38703 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499613) = 1/(2499613 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_632 : Bounds (-38703 / 250000000) (-154811 / 1000000000) (Real.log (2499613 / 2500000)) := by
  have h := reflection_log_632_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_633_neg : (74744697 / 1000000000) ≤ -Real.log (1000000 / 1077609) ∧
    -Real.log (1000000 / 1077609) ≤ (37372349 / 500000000) := by
  have h := checkLog_sound (w := (77609 / 2077609)) (n := 12)
    (lo := (74744697 / 1000000000)) (hi := (37372349 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1077609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1077609 / 1000000) = 1/(1000000 / 1077609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_633 : Bounds (74744697 / 1000000000) (37372349 / 500000000) (Real.log (1077609 / 1000000)) := by
  have h := reflection_log_633_neg
  have he : Real.log (1077609 / 1000000) = -Real.log (1000000 / 1077609) := by
    rw [show ((1077609 / 1000000) : ℝ) = ((1000000 / 1077609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_634_neg : (80786067 / 1000000000) ≤ -Real.log (922391 / 1000000) ∧
    -Real.log (922391 / 1000000) ≤ (20196517 / 250000000) := by
  have h := checkLog_sound (w := (77609 / 1922391)) (n := 12)
    (lo := (80786067 / 1000000000)) (hi := (20196517 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 922391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 922391) = 1/(922391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_634 : Bounds (-20196517 / 250000000) (-80786067 / 1000000000) (Real.log (922391 / 1000000)) := by
  have h := reflection_log_634_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_635_neg : (14986983 / 200000000) ≤ -Real.log (500000 / 538907) ∧
    -Real.log (500000 / 538907) ≤ (18733729 / 250000000) := by
  have h := checkLog_sound (w := (38907 / 1038907)) (n := 12)
    (lo := (14986983 / 200000000)) (hi := (18733729 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((538907 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(538907 / 500000) = 1/(500000 / 538907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_635 : Bounds (14986983 / 200000000) (18733729 / 250000000) (Real.log (538907 / 500000)) := by
  have h := reflection_log_635_neg
  have he : Real.log (538907 / 500000) = -Real.log (500000 / 538907) := by
    rw [show ((538907 / 500000) : ℝ) = ((500000 / 538907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_636_neg : (4050417 / 50000000) ≤ -Real.log (461093 / 500000) ∧
    -Real.log (461093 / 500000) ≤ (81008341 / 1000000000) := by
  have h := checkLog_sound (w := (38907 / 961093)) (n := 12)
    (lo := (4050417 / 50000000)) (hi := (81008341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 461093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 461093) = 1/(461093 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_636 : Bounds (-81008341 / 1000000000) (-4050417 / 50000000) (Real.log (461093 / 500000)) := by
  have h := reflection_log_636_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_637_neg : (379589 / 62500000) ≤ -Real.log (248486245351 / 250000000000) ∧
    -Real.log (248486245351 / 250000000000) ≤ (242937 / 40000000) := by
  have h := checkLog_sound (w := (1513754649 / 498486245351)) (n := 12)
    (lo := (379589 / 62500000)) (hi := (242937 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248486245351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248486245351) = 1/(248486245351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_637 : Bounds (-242937 / 40000000) (-379589 / 62500000) (Real.log (248486245351 / 250000000000)) := by
  have h := reflection_log_637_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_638_neg : (6041369 / 1000000000) ≤ -Real.log (993976843119 / 1000000000000) ∧
    -Real.log (993976843119 / 1000000000000) ≤ (604137 / 100000000) := by
  have h := checkLog_sound (w := (6023156881 / 1993976843119)) (n := 12)
    (lo := (6041369 / 1000000000)) (hi := (604137 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993976843119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993976843119) = 1/(993976843119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_638 : Bounds (-604137 / 100000000) (-6041369 / 1000000000) (Real.log (993976843119 / 1000000000000)) := by
  have h := reflection_log_638_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_639_neg : (31106153 / 200000000) ≤ -Real.log (500000000000 / 584138938909) ∧
    -Real.log (500000000000 / 584138938909) ≤ (77765383 / 500000000) := by
  have h := checkLog_sound (w := (84138938909 / 1084138938909)) (n := 12)
    (lo := (31106153 / 200000000)) (hi := (77765383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((584138938909 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(584138938909 / 500000000000) = 1/(500000000000 / 584138938909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_639 : Bounds (31106153 / 200000000) (77765383 / 500000000) (Real.log (584138938909 / 500000000000)) := by
  have h := reflection_log_639_neg
  have he : Real.log (584138938909 / 500000000000) = -Real.log (500000000000 / 584138938909) := by
    rw [show ((584138938909 / 500000000000) : ℝ) = ((500000000000 / 584138938909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
