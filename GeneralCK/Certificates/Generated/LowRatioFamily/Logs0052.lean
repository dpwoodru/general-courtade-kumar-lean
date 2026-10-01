import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_3328_neg : (342933 / 1953125) ≤ -Real.log (100000000000 / 119193936219) ∧
    -Real.log (100000000000 / 119193936219) ≤ (175581697 / 1000000000) := by
  have h := checkLog_sound (w := (19193936219 / 219193936219)) (n := 12)
    (lo := (342933 / 1953125)) (hi := (175581697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119193936219 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119193936219 / 100000000000) = 1/(100000000000 / 119193936219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3328 : Bounds (342933 / 1953125) (175581697 / 1000000000) (Real.log (119193936219 / 100000000000)) := by
  have h := reflection_log_3328_neg
  have he : Real.log (119193936219 / 100000000000) = -Real.log (100000000000 / 119193936219) := by
    rw [show ((119193936219 / 100000000000) : ℝ) = ((100000000000 / 119193936219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3329_neg : (175685493 / 500000000) ≤ -Real.log (500000000000 / 710507202517) ∧
    -Real.log (500000000000 / 710507202517) ≤ (351370987 / 1000000000) := by
  have h := checkLog_sound (w := (210507202517 / 1210507202517)) (n := 12)
    (lo := (175685493 / 500000000)) (hi := (351370987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((710507202517 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(710507202517 / 500000000000) = 1/(500000000000 / 710507202517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3329 : Bounds (175685493 / 500000000) (351370987 / 1000000000) (Real.log (710507202517 / 500000000000)) := by
  have h := reflection_log_3329_neg
  have he : Real.log (710507202517 / 500000000000) = -Real.log (500000000000 / 710507202517) := by
    rw [show ((710507202517 / 500000000000) : ℝ) = ((500000000000 / 710507202517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3330_neg : (175788613 / 500000000) ≤ -Real.log (500000000000 / 710653753027) ∧
    -Real.log (500000000000 / 710653753027) ≤ (351577227 / 1000000000) := by
  have h := checkLog_sound (w := (210653753027 / 1210653753027)) (n := 12)
    (lo := (175788613 / 500000000)) (hi := (351577227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((710653753027 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(710653753027 / 500000000000) = 1/(500000000000 / 710653753027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3330 : Bounds (175788613 / 500000000) (351577227 / 1000000000) (Real.log (710653753027 / 500000000000)) := by
  have h := reflection_log_3330_neg
  have he : Real.log (710653753027 / 500000000000) = -Real.log (500000000000 / 710653753027) := by
    rw [show ((710653753027 / 500000000000) : ℝ) = ((500000000000 / 710653753027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3331_neg : (20062737 / 125000000) ≤ -Real.log (10000 / 11741) ∧
    -Real.log (10000 / 11741) ≤ (160501897 / 1000000000) := by
  have h := checkLog_sound (w := (1741 / 21741)) (n := 12)
    (lo := (20062737 / 125000000)) (hi := (160501897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11741 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11741 / 10000) = 1/(10000 / 11741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3331 : Bounds (20062737 / 125000000) (160501897 / 1000000000) (Real.log (11741 / 10000)) := by
  have h := reflection_log_3331_neg
  have he : Real.log (11741 / 10000) = -Real.log (10000 / 11741) := by
    rw [show ((11741 / 10000) : ℝ) = ((10000 / 11741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3332_neg : (95640789 / 500000000) ≤ -Real.log (8259 / 10000) ∧
    -Real.log (8259 / 10000) ≤ (191281579 / 1000000000) := by
  have h := checkLog_sound (w := (1741 / 18259)) (n := 12)
    (lo := (95640789 / 500000000)) (hi := (191281579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8259) = 1/(8259 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3332 : Bounds (-191281579 / 1000000000) (-95640789 / 500000000) (Real.log (8259 / 10000)) := by
  have h := reflection_log_3332_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3333_neg : (43521 / 250000000) ≤ -Real.log (10000000 / 10001741) ∧
    -Real.log (10000000 / 10001741) ≤ (34817 / 200000000) := by
  have h := checkLog_sound (w := (1741 / 20001741)) (n := 12)
    (lo := (43521 / 250000000)) (hi := (34817 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001741 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001741 / 10000000) = 1/(10000000 / 10001741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3333 : Bounds (43521 / 250000000) (34817 / 200000000) (Real.log (10001741 / 10000000)) := by
  have h := reflection_log_3333_neg
  have he : Real.log (10001741 / 10000000) = -Real.log (10000000 / 10001741) := by
    rw [show ((10001741 / 10000000) : ℝ) = ((10000000 / 10001741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3334_neg : (34823 / 200000000) ≤ -Real.log (9998259 / 10000000) ∧
    -Real.log (9998259 / 10000000) ≤ (43529 / 250000000) := by
  have h := checkLog_sound (w := (1741 / 19998259)) (n := 12)
    (lo := (34823 / 200000000)) (hi := (43529 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998259) = 1/(9998259 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3334 : Bounds (-43529 / 250000000) (-34823 / 200000000) (Real.log (9998259 / 10000000)) := by
  have h := reflection_log_3334_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3335_neg : (10472771 / 125000000) ≤ -Real.log (31250 / 33981) ∧
    -Real.log (31250 / 33981) ≤ (83782169 / 1000000000) := by
  have h := checkLog_sound (w := (2731 / 65231)) (n := 12)
    (lo := (10472771 / 125000000)) (hi := (83782169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33981 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33981 / 31250) = 1/(31250 / 33981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3335 : Bounds (10472771 / 125000000) (83782169 / 1000000000) (Real.log (33981 / 31250)) := by
  have h := reflection_log_3335_neg
  have he : Real.log (33981 / 31250) = -Real.log (31250 / 33981) := by
    rw [show ((33981 / 31250) : ℝ) = ((31250 / 33981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3336_neg : (22862211 / 250000000) ≤ -Real.log (28519 / 31250) ∧
    -Real.log (28519 / 31250) ≤ (18289769 / 200000000) := by
  have h := checkLog_sound (w := (2731 / 59769)) (n := 12)
    (lo := (22862211 / 250000000)) (hi := (18289769 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 28519) = 1/(28519 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3336 : Bounds (-18289769 / 200000000) (-22862211 / 250000000) (Real.log (28519 / 31250)) := by
  have h := reflection_log_3336_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3337_neg : (10498633 / 125000000) ≤ -Real.log (1000000 / 1087617) ∧
    -Real.log (1000000 / 1087617) ≤ (16797813 / 200000000) := by
  have h := checkLog_sound (w := (87617 / 2087617)) (n := 12)
    (lo := (10498633 / 125000000)) (hi := (16797813 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087617 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087617 / 1000000) = 1/(1000000 / 1087617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3337 : Bounds (10498633 / 125000000) (16797813 / 200000000) (Real.log (1087617 / 1000000)) := by
  have h := reflection_log_3337_neg
  have he : Real.log (1087617 / 1000000) = -Real.log (1000000 / 1087617) := by
    rw [show ((1087617 / 1000000) : ℝ) = ((1000000 / 1087617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3338_neg : (4584771 / 50000000) ≤ -Real.log (912383 / 1000000) ∧
    -Real.log (912383 / 1000000) ≤ (91695421 / 1000000000) := by
  have h := checkLog_sound (w := (87617 / 1912383)) (n := 12)
    (lo := (4584771 / 50000000)) (hi := (91695421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912383) = 1/(912383 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3338 : Bounds (-91695421 / 1000000000) (-4584771 / 50000000) (Real.log (912383 / 1000000)) := by
  have h := reflection_log_3338_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3339_neg : (1926589 / 250000000) ≤ -Real.log (992323261311 / 1000000000000) ∧
    -Real.log (992323261311 / 1000000000000) ≤ (7706357 / 1000000000) := by
  have h := checkLog_sound (w := (7676738689 / 1992323261311)) (n := 12)
    (lo := (1926589 / 250000000)) (hi := (7706357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992323261311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992323261311) = 1/(992323261311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3339 : Bounds (-7706357 / 1000000000) (-1926589 / 250000000) (Real.log (992323261311 / 1000000000000)) := by
  have h := reflection_log_3339_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3340_neg : (306667 / 40000000) ≤ -Real.log (969104139 / 976562500) ∧
    -Real.log (969104139 / 976562500) ≤ (1916669 / 250000000) := by
  have h := checkLog_sound (w := (7458361 / 1945666639)) (n := 12)
    (lo := (306667 / 40000000)) (hi := (1916669 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 969104139) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 969104139) = 1/(969104139 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3340 : Bounds (-1916669 / 250000000) (-306667 / 40000000) (Real.log (969104139 / 976562500)) := by
  have h := reflection_log_3340_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3341_neg : (175231013 / 1000000000) ≤ -Real.log (250000000000 / 297880360461) ∧
    -Real.log (250000000000 / 297880360461) ≤ (87615507 / 500000000) := by
  have h := checkLog_sound (w := (47880360461 / 547880360461)) (n := 12)
    (lo := (175231013 / 1000000000)) (hi := (87615507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297880360461 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297880360461 / 250000000000) = 1/(250000000000 / 297880360461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3341 : Bounds (175231013 / 1000000000) (87615507 / 500000000) (Real.log (297880360461 / 250000000000)) := by
  have h := reflection_log_3341_neg
  have he : Real.log (297880360461 / 250000000000) = -Real.log (250000000000 / 297880360461) := by
    rw [show ((297880360461 / 250000000000) : ℝ) = ((250000000000 / 297880360461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3342_neg : (35136897 / 200000000) ≤ -Real.log (250000000000 / 298015471573) ∧
    -Real.log (250000000000 / 298015471573) ≤ (87842243 / 500000000) := by
  have h := checkLog_sound (w := (48015471573 / 548015471573)) (n := 12)
    (lo := (35136897 / 200000000)) (hi := (87842243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298015471573 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298015471573 / 250000000000) = 1/(250000000000 / 298015471573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3342 : Bounds (35136897 / 200000000) (87842243 / 500000000) (Real.log (298015471573 / 250000000000)) := by
  have h := reflection_log_3342_neg
  have he : Real.log (298015471573 / 250000000000) = -Real.log (250000000000 / 298015471573) := by
    rw [show ((298015471573 / 250000000000) : ℝ) = ((250000000000 / 298015471573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3343_neg : (175788613 / 500000000) ≤ -Real.log (250000000000 / 355326876513) ∧
    -Real.log (250000000000 / 355326876513) ≤ (351577227 / 1000000000) := by
  have h := checkLog_sound (w := (105326876513 / 605326876513)) (n := 12)
    (lo := (175788613 / 500000000)) (hi := (351577227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355326876513 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355326876513 / 250000000000) = 1/(250000000000 / 355326876513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3343 : Bounds (175788613 / 500000000) (351577227 / 1000000000) (Real.log (355326876513 / 250000000000)) := by
  have h := reflection_log_3343_neg
  have he : Real.log (355326876513 / 250000000000) = -Real.log (250000000000 / 355326876513) := by
    rw [show ((355326876513 / 250000000000) : ℝ) = ((250000000000 / 355326876513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3344_neg : (175891737 / 500000000) ≤ -Real.log (20000000000 / 28432013561) ∧
    -Real.log (20000000000 / 28432013561) ≤ (14071339 / 40000000) := by
  have h := checkLog_sound (w := (8432013561 / 48432013561)) (n := 12)
    (lo := (175891737 / 500000000)) (hi := (14071339 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28432013561 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(28432013561 / 20000000000) = 1/(20000000000 / 28432013561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3344 : Bounds (175891737 / 500000000) (14071339 / 40000000) (Real.log (28432013561 / 20000000000)) := by
  have h := reflection_log_3344_neg
  have he : Real.log (28432013561 / 20000000000) = -Real.log (20000000000 / 28432013561) := by
    rw [show ((28432013561 / 20000000000) : ℝ) = ((20000000000 / 28432013561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3345_neg : (20073383 / 125000000) ≤ -Real.log (5000 / 5871) ∧
    -Real.log (5000 / 5871) ≤ (32117413 / 200000000) := by
  have h := checkLog_sound (w := (871 / 10871)) (n := 12)
    (lo := (20073383 / 125000000)) (hi := (32117413 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5871 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5871 / 5000) = 1/(5000 / 5871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3345 : Bounds (20073383 / 125000000) (32117413 / 200000000) (Real.log (5871 / 5000)) := by
  have h := reflection_log_3345_neg
  have he : Real.log (5871 / 5000) = -Real.log (5000 / 5871) := by
    rw [show ((5871 / 5000) : ℝ) = ((5000 / 5871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3346_neg : (38280533 / 200000000) ≤ -Real.log (4129 / 5000) ∧
    -Real.log (4129 / 5000) ≤ (95701333 / 500000000) := by
  have h := checkLog_sound (w := (871 / 9129)) (n := 12)
    (lo := (38280533 / 200000000)) (hi := (95701333 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4129) = 1/(4129 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3346 : Bounds (-95701333 / 500000000) (-38280533 / 200000000) (Real.log (4129 / 5000)) := by
  have h := reflection_log_3346_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3347_neg : (21773 / 125000000) ≤ -Real.log (5000000 / 5000871) ∧
    -Real.log (5000000 / 5000871) ≤ (34837 / 200000000) := by
  have h := checkLog_sound (w := (871 / 10000871)) (n := 12)
    (lo := (21773 / 125000000)) (hi := (34837 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000871 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000871 / 5000000) = 1/(5000000 / 5000871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3347 : Bounds (21773 / 125000000) (34837 / 200000000) (Real.log (5000871 / 5000000)) := by
  have h := reflection_log_3347_neg
  have he : Real.log (5000871 / 5000000) = -Real.log (5000000 / 5000871) := by
    rw [show ((5000871 / 5000000) : ℝ) = ((5000000 / 5000871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3348_neg : (34843 / 200000000) ≤ -Real.log (4999129 / 5000000) ∧
    -Real.log (4999129 / 5000000) ≤ (21777 / 125000000) := by
  have h := checkLog_sound (w := (871 / 9999129)) (n := 12)
    (lo := (34843 / 200000000)) (hi := (21777 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999129) = 1/(4999129 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3348 : Bounds (-21777 / 125000000) (-34843 / 200000000) (Real.log (4999129 / 5000000)) := by
  have h := reflection_log_3348_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3349_neg : (20957267 / 250000000) ≤ -Real.log (1000000 / 1087443) ∧
    -Real.log (1000000 / 1087443) ≤ (83829069 / 1000000000) := by
  have h := checkLog_sound (w := (87443 / 2087443)) (n := 12)
    (lo := (20957267 / 250000000)) (hi := (83829069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087443 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087443 / 1000000) = 1/(1000000 / 1087443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3349 : Bounds (20957267 / 250000000) (83829069 / 1000000000) (Real.log (1087443 / 1000000)) := by
  have h := reflection_log_3349_neg
  have he : Real.log (1087443 / 1000000) = -Real.log (1000000 / 1087443) := by
    rw [show ((1087443 / 1000000) : ℝ) = ((1000000 / 1087443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3350_neg : (91504729 / 1000000000) ≤ -Real.log (912557 / 1000000) ∧
    -Real.log (912557 / 1000000) ≤ (9150473 / 100000000) := by
  have h := checkLog_sound (w := (87443 / 1912557)) (n := 12)
    (lo := (91504729 / 1000000000)) (hi := (9150473 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912557) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912557) = 1/(912557 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3350 : Bounds (-9150473 / 100000000) (-91504729 / 1000000000) (Real.log (912557 / 1000000)) := by
  have h := reflection_log_3350_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3351_neg : (42017977 / 500000000) ≤ -Real.log (250000 / 271917) ∧
    -Real.log (250000 / 271917) ≤ (16807191 / 200000000) := by
  have h := checkLog_sound (w := (21917 / 521917)) (n := 12)
    (lo := (42017977 / 500000000)) (hi := (16807191 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271917 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271917 / 250000) = 1/(250000 / 271917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3351 : Bounds (42017977 / 500000000) (16807191 / 200000000) (Real.log (271917 / 250000)) := by
  have h := reflection_log_3351_neg
  have he : Real.log (271917 / 250000) = -Real.log (250000 / 271917) := by
    rw [show ((271917 / 250000) : ℝ) = ((250000 / 271917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3352_neg : (2293783 / 25000000) ≤ -Real.log (228083 / 250000) ∧
    -Real.log (228083 / 250000) ≤ (91751321 / 1000000000) := by
  have h := checkLog_sound (w := (21917 / 478083)) (n := 12)
    (lo := (2293783 / 25000000)) (hi := (91751321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 228083) = 1/(228083 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3352 : Bounds (-91751321 / 1000000000) (-2293783 / 25000000) (Real.log (228083 / 250000)) := by
  have h := reflection_log_3352_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3353_neg : (1543073 / 200000000) ≤ -Real.log (62019645111 / 62500000000) ∧
    -Real.log (62019645111 / 62500000000) ≤ (3857683 / 500000000) := by
  have h := checkLog_sound (w := (480354889 / 124519645111)) (n := 12)
    (lo := (1543073 / 200000000)) (hi := (3857683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62019645111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62019645111) = 1/(62019645111 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3353 : Bounds (-3857683 / 500000000) (-1543073 / 200000000) (Real.log (62019645111 / 62500000000)) := by
  have h := reflection_log_3353_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3354_neg : (383783 / 50000000) ≤ -Real.log (992353721751 / 1000000000000) ∧
    -Real.log (992353721751 / 1000000000000) ≤ (7675661 / 1000000000) := by
  have h := checkLog_sound (w := (7646278249 / 1992353721751)) (n := 12)
    (lo := (383783 / 50000000)) (hi := (7675661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992353721751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992353721751) = 1/(992353721751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3354 : Bounds (-7675661 / 1000000000) (-383783 / 50000000) (Real.log (992353721751 / 1000000000000)) := by
  have h := reflection_log_3354_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3355_neg : (87666899 / 500000000) ≤ -Real.log (250000000000 / 297910979807) ∧
    -Real.log (250000000000 / 297910979807) ≤ (175333799 / 1000000000) := by
  have h := checkLog_sound (w := (47910979807 / 547910979807)) (n := 12)
    (lo := (87666899 / 500000000)) (hi := (175333799 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297910979807 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297910979807 / 250000000000) = 1/(250000000000 / 297910979807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3355 : Bounds (87666899 / 500000000) (175333799 / 1000000000) (Real.log (297910979807 / 250000000000)) := by
  have h := reflection_log_3355_neg
  have he : Real.log (297910979807 / 250000000000) = -Real.log (250000000000 / 297910979807) := by
    rw [show ((297910979807 / 250000000000) : ℝ) = ((250000000000 / 297910979807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3356_neg : (87893637 / 500000000) ≤ -Real.log (250000000000 / 298046106023) ∧
    -Real.log (250000000000 / 298046106023) ≤ (7031491 / 40000000) := by
  have h := checkLog_sound (w := (48046106023 / 548046106023)) (n := 12)
    (lo := (87893637 / 500000000)) (hi := (7031491 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298046106023 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298046106023 / 250000000000) = 1/(250000000000 / 298046106023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3356 : Bounds (87893637 / 500000000) (7031491 / 40000000) (Real.log (298046106023 / 250000000000)) := by
  have h := reflection_log_3356_neg
  have he : Real.log (298046106023 / 250000000000) = -Real.log (250000000000 / 298046106023) := by
    rw [show ((298046106023 / 250000000000) : ℝ) = ((250000000000 / 298046106023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3357_neg : (175891737 / 500000000) ≤ -Real.log (31250000000 / 44425021189) ∧
    -Real.log (31250000000 / 44425021189) ≤ (14071339 / 40000000) := by
  have h := checkLog_sound (w := (13175021189 / 75675021189)) (n := 12)
    (lo := (175891737 / 500000000)) (hi := (14071339 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44425021189 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44425021189 / 31250000000) = 1/(31250000000 / 44425021189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3357 : Bounds (175891737 / 500000000) (14071339 / 40000000) (Real.log (44425021189 / 31250000000)) := by
  have h := reflection_log_3357_neg
  have he : Real.log (44425021189 / 31250000000) = -Real.log (31250000000 / 44425021189) := by
    rw [show ((44425021189 / 31250000000) : ℝ) = ((31250000000 / 44425021189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3358_neg : (35198973 / 100000000) ≤ -Real.log (125000000000 / 177736740131) ∧
    -Real.log (125000000000 / 177736740131) ≤ (351989731 / 1000000000) := by
  have h := checkLog_sound (w := (52736740131 / 302736740131)) (n := 12)
    (lo := (35198973 / 100000000)) (hi := (351989731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177736740131 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177736740131 / 125000000000) = 1/(125000000000 / 177736740131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3358 : Bounds (35198973 / 100000000) (351989731 / 1000000000) (Real.log (177736740131 / 125000000000)) := by
  have h := reflection_log_3358_neg
  have he : Real.log (177736740131 / 125000000000) = -Real.log (125000000000 / 177736740131) := by
    rw [show ((177736740131 / 125000000000) : ℝ) = ((125000000000 / 177736740131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3359_neg : (6426889 / 40000000) ≤ -Real.log (10000 / 11743) ∧
    -Real.log (10000 / 11743) ≤ (80336113 / 500000000) := by
  have h := checkLog_sound (w := (1743 / 21743)) (n := 12)
    (lo := (6426889 / 40000000)) (hi := (80336113 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11743 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11743 / 10000) = 1/(10000 / 11743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3359 : Bounds (6426889 / 40000000) (80336113 / 500000000) (Real.log (11743 / 10000)) := by
  have h := reflection_log_3359_neg
  have he : Real.log (11743 / 10000) = -Real.log (10000 / 11743) := by
    rw [show ((11743 / 10000) : ℝ) = ((10000 / 11743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3360_neg : (191523767 / 1000000000) ≤ -Real.log (8257 / 10000) ∧
    -Real.log (8257 / 10000) ≤ (23940471 / 125000000) := by
  have h := checkLog_sound (w := (1743 / 18257)) (n := 12)
    (lo := (191523767 / 1000000000)) (hi := (23940471 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8257) = 1/(8257 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3360 : Bounds (-23940471 / 125000000) (-191523767 / 1000000000) (Real.log (8257 / 10000)) := by
  have h := reflection_log_3360_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3361_neg : (43571 / 250000000) ≤ -Real.log (10000000 / 10001743) ∧
    -Real.log (10000000 / 10001743) ≤ (34857 / 200000000) := by
  have h := checkLog_sound (w := (1743 / 20001743)) (n := 12)
    (lo := (43571 / 250000000)) (hi := (34857 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001743 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001743 / 10000000) = 1/(10000000 / 10001743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3361 : Bounds (43571 / 250000000) (34857 / 200000000) (Real.log (10001743 / 10000000)) := by
  have h := reflection_log_3361_neg
  have he : Real.log (10001743 / 10000000) = -Real.log (10000000 / 10001743) := by
    rw [show ((10001743 / 10000000) : ℝ) = ((10000000 / 10001743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3362_neg : (34863 / 200000000) ≤ -Real.log (9998257 / 10000000) ∧
    -Real.log (9998257 / 10000000) ≤ (43579 / 250000000) := by
  have h := checkLog_sound (w := (1743 / 19998257)) (n := 12)
    (lo := (34863 / 200000000)) (hi := (43579 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998257) = 1/(9998257 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3362 : Bounds (-43579 / 250000000) (-34863 / 200000000) (Real.log (9998257 / 10000000)) := by
  have h := reflection_log_3362_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3363_neg : (41937983 / 500000000) ≤ -Real.log (500000 / 543747) ∧
    -Real.log (500000 / 543747) ≤ (83875967 / 1000000000) := by
  have h := checkLog_sound (w := (43747 / 1043747)) (n := 12)
    (lo := (41937983 / 500000000)) (hi := (83875967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543747 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(543747 / 500000) = 1/(500000 / 543747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3363 : Bounds (41937983 / 500000000) (83875967 / 1000000000) (Real.log (543747 / 500000)) := by
  have h := reflection_log_3363_neg
  have he : Real.log (543747 / 500000) = -Real.log (500000 / 543747) := by
    rw [show ((543747 / 500000) : ℝ) = ((500000 / 543747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3364_neg : (45780309 / 500000000) ≤ -Real.log (456253 / 500000) ∧
    -Real.log (456253 / 500000) ≤ (91560619 / 1000000000) := by
  have h := checkLog_sound (w := (43747 / 956253)) (n := 12)
    (lo := (45780309 / 500000000)) (hi := (91560619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 456253) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 456253) = 1/(456253 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3364 : Bounds (-91560619 / 1000000000) (-45780309 / 500000000) (Real.log (456253 / 500000)) := by
  have h := reflection_log_3364_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3365_neg : (84082843 / 1000000000) ≤ -Real.log (1000000 / 1087719) ∧
    -Real.log (1000000 / 1087719) ≤ (21020711 / 250000000) := by
  have h := checkLog_sound (w := (87719 / 2087719)) (n := 12)
    (lo := (84082843 / 1000000000)) (hi := (21020711 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1087719 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1087719 / 1000000) = 1/(1000000 / 1087719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3365 : Bounds (84082843 / 1000000000) (21020711 / 250000000) (Real.log (1087719 / 1000000)) := by
  have h := reflection_log_3365_neg
  have he : Real.log (1087719 / 1000000) = -Real.log (1000000 / 1087719) := by
    rw [show ((1087719 / 1000000) : ℝ) = ((1000000 / 1087719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3366_neg : (45903611 / 500000000) ≤ -Real.log (912281 / 1000000) ∧
    -Real.log (912281 / 1000000) ≤ (91807223 / 1000000000) := by
  have h := checkLog_sound (w := (87719 / 1912281)) (n := 12)
    (lo := (45903611 / 500000000)) (hi := (91807223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 912281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 912281) = 1/(912281 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3366 : Bounds (-91807223 / 1000000000) (-45903611 / 500000000) (Real.log (912281 / 1000000)) := by
  have h := reflection_log_3366_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3367_neg : (7724379 / 1000000000) ≤ -Real.log (992305377039 / 1000000000000) ∧
    -Real.log (992305377039 / 1000000000000) ≤ (386219 / 50000000) := by
  have h := checkLog_sound (w := (7694622961 / 1992305377039)) (n := 12)
    (lo := (7724379 / 1000000000)) (hi := (386219 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992305377039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992305377039) = 1/(992305377039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3367 : Bounds (-386219 / 50000000) (-7724379 / 1000000000) (Real.log (992305377039 / 1000000000000)) := by
  have h := reflection_log_3367_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3368_neg : (7684651 / 1000000000) ≤ -Real.log (248086199991 / 250000000000) ∧
    -Real.log (248086199991 / 250000000000) ≤ (1921163 / 250000000) := by
  have h := checkLog_sound (w := (1913800009 / 498086199991)) (n := 12)
    (lo := (7684651 / 1000000000)) (hi := (1921163 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248086199991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248086199991) = 1/(248086199991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3368 : Bounds (-1921163 / 250000000) (-7684651 / 1000000000) (Real.log (248086199991 / 250000000000)) := by
  have h := reflection_log_3368_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3369_neg : (21929573 / 125000000) ≤ -Real.log (500000000000 / 595883205151) ∧
    -Real.log (500000000000 / 595883205151) ≤ (35087317 / 200000000) := by
  have h := checkLog_sound (w := (95883205151 / 1095883205151)) (n := 12)
    (lo := (21929573 / 125000000)) (hi := (35087317 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((595883205151 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(595883205151 / 500000000000) = 1/(500000000000 / 595883205151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3369 : Bounds (21929573 / 125000000) (35087317 / 200000000) (Real.log (595883205151 / 500000000000)) := by
  have h := reflection_log_3369_neg
  have he : Real.log (595883205151 / 500000000000) = -Real.log (500000000000 / 595883205151) := by
    rw [show ((595883205151 / 500000000000) : ℝ) = ((500000000000 / 595883205151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3370_neg : (35178013 / 200000000) ≤ -Real.log (125000000000 / 149038371949) ∧
    -Real.log (125000000000 / 149038371949) ≤ (87945033 / 500000000) := by
  have h := checkLog_sound (w := (24038371949 / 274038371949)) (n := 12)
    (lo := (35178013 / 200000000)) (hi := (87945033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149038371949 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149038371949 / 125000000000) = 1/(125000000000 / 149038371949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3370 : Bounds (35178013 / 200000000) (87945033 / 500000000) (Real.log (149038371949 / 125000000000)) := by
  have h := reflection_log_3370_neg
  have he : Real.log (149038371949 / 125000000000) = -Real.log (125000000000 / 149038371949) := by
    rw [show ((149038371949 / 125000000000) : ℝ) = ((125000000000 / 149038371949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3371_neg : (35198973 / 100000000) ≤ -Real.log (500000000000 / 710946960523) ∧
    -Real.log (500000000000 / 710946960523) ≤ (351989731 / 1000000000) := by
  have h := checkLog_sound (w := (210946960523 / 1210946960523)) (n := 12)
    (lo := (35198973 / 100000000)) (hi := (351989731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((710946960523 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(710946960523 / 500000000000) = 1/(500000000000 / 710946960523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3371 : Bounds (35198973 / 100000000) (351989731 / 1000000000) (Real.log (710946960523 / 500000000000)) := by
  have h := reflection_log_3371_neg
  have he : Real.log (710946960523 / 500000000000) = -Real.log (500000000000 / 710946960523) := by
    rw [show ((710946960523 / 500000000000) : ℝ) = ((500000000000 / 710946960523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3372_neg : (44024499 / 125000000) ≤ -Real.log (500000000000 / 711093617537) ∧
    -Real.log (500000000000 / 711093617537) ≤ (352195993 / 1000000000) := by
  have h := checkLog_sound (w := (211093617537 / 1211093617537)) (n := 12)
    (lo := (44024499 / 125000000)) (hi := (352195993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711093617537 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711093617537 / 500000000000) = 1/(500000000000 / 711093617537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3372 : Bounds (44024499 / 125000000) (352195993 / 1000000000) (Real.log (711093617537 / 500000000000)) := by
  have h := reflection_log_3372_neg
  have he : Real.log (711093617537 / 500000000000) = -Real.log (500000000000 / 711093617537) := by
    rw [show ((711093617537 / 500000000000) : ℝ) = ((500000000000 / 711093617537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3373_neg : (80378689 / 500000000) ≤ -Real.log (625 / 734) ∧
    -Real.log (625 / 734) ≤ (160757379 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 1359)) (n := 12)
    (lo := (80378689 / 500000000)) (hi := (160757379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((734 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(734 / 625) = 1/(625 / 734) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3373 : Bounds (80378689 / 500000000) (160757379 / 1000000000) (Real.log (734 / 625)) := by
  have h := reflection_log_3373_neg
  have he : Real.log (734 / 625) = -Real.log (625 / 734) := by
    rw [show ((734 / 625) : ℝ) = ((625 / 734) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3374_neg : (47911221 / 250000000) ≤ -Real.log (516 / 625) ∧
    -Real.log (516 / 625) ≤ (38328977 / 200000000) := by
  have h := checkLog_sound (w := (109 / 1141)) (n := 12)
    (lo := (47911221 / 250000000)) (hi := (38328977 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 516) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 516) = 1/(516 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3374 : Bounds (-38328977 / 200000000) (-47911221 / 250000000) (Real.log (516 / 625)) := by
  have h := reflection_log_3374_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3375_neg : (10899 / 62500000) ≤ -Real.log (625000 / 625109) ∧
    -Real.log (625000 / 625109) ≤ (34877 / 200000000) := by
  have h := checkLog_sound (w := (109 / 1250109)) (n := 12)
    (lo := (10899 / 62500000)) (hi := (34877 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625109 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625109 / 625000) = 1/(625000 / 625109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3375 : Bounds (10899 / 62500000) (34877 / 200000000) (Real.log (625109 / 625000)) := by
  have h := reflection_log_3375_neg
  have he : Real.log (625109 / 625000) = -Real.log (625000 / 625109) := by
    rw [show ((625109 / 625000) : ℝ) = ((625000 / 625109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3376_neg : (34883 / 200000000) ≤ -Real.log (624891 / 625000) ∧
    -Real.log (624891 / 625000) ≤ (10901 / 62500000) := by
  have h := checkLog_sound (w := (109 / 1249891)) (n := 12)
    (lo := (34883 / 200000000)) (hi := (10901 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624891) = 1/(624891 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3376 : Bounds (-10901 / 62500000) (-34883 / 200000000) (Real.log (624891 / 625000)) := by
  have h := reflection_log_3376_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3377_neg : (41961431 / 500000000) ≤ -Real.log (200000 / 217509) ∧
    -Real.log (200000 / 217509) ≤ (83922863 / 1000000000) := by
  have h := checkLog_sound (w := (17509 / 417509)) (n := 12)
    (lo := (41961431 / 500000000)) (hi := (83922863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217509 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217509 / 200000) = 1/(200000 / 217509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3377 : Bounds (41961431 / 500000000) (83922863 / 1000000000) (Real.log (217509 / 200000)) := by
  have h := reflection_log_3377_neg
  have he : Real.log (217509 / 200000) = -Real.log (200000 / 217509) := by
    rw [show ((217509 / 200000) : ℝ) = ((200000 / 217509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3378_neg : (91616509 / 1000000000) ≤ -Real.log (182491 / 200000) ∧
    -Real.log (182491 / 200000) ≤ (9161651 / 100000000) := by
  have h := checkLog_sound (w := (17509 / 382491)) (n := 12)
    (lo := (91616509 / 1000000000)) (hi := (9161651 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182491) = 1/(182491 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3378 : Bounds (-9161651 / 100000000) (-91616509 / 1000000000) (Real.log (182491 / 200000)) := by
  have h := reflection_log_3378_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3379_neg : (84129729 / 1000000000) ≤ -Real.log (100000 / 108777) ∧
    -Real.log (100000 / 108777) ≤ (8412973 / 100000000) := by
  have h := checkLog_sound (w := (8777 / 208777)) (n := 12)
    (lo := (84129729 / 1000000000)) (hi := (8412973 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108777 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108777 / 100000) = 1/(100000 / 108777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3379 : Bounds (84129729 / 1000000000) (8412973 / 100000000) (Real.log (108777 / 100000)) := by
  have h := reflection_log_3379_neg
  have he : Real.log (108777 / 100000) = -Real.log (100000 / 108777) := by
    rw [show ((108777 / 100000) : ℝ) = ((100000 / 108777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3380_neg : (91863127 / 1000000000) ≤ -Real.log (91223 / 100000) ∧
    -Real.log (91223 / 100000) ≤ (11482891 / 125000000) := by
  have h := checkLog_sound (w := (8777 / 191223)) (n := 12)
    (lo := (91863127 / 1000000000)) (hi := (11482891 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 91223) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 91223) = 1/(91223 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3380 : Bounds (-11482891 / 125000000) (-91863127 / 1000000000) (Real.log (91223 / 100000)) := by
  have h := reflection_log_3380_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3381_neg : (3866699 / 500000000) ≤ -Real.log (9922964271 / 10000000000) ∧
    -Real.log (9922964271 / 10000000000) ≤ (7733399 / 1000000000) := by
  have h := checkLog_sound (w := (77035729 / 19922964271)) (n := 12)
    (lo := (3866699 / 500000000)) (hi := (7733399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9922964271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9922964271) = 1/(9922964271 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3381 : Bounds (-7733399 / 1000000000) (-3866699 / 500000000) (Real.log (9922964271 / 10000000000)) := by
  have h := reflection_log_3381_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3382_neg : (7693647 / 1000000000) ≤ -Real.log (39693434919 / 40000000000) ∧
    -Real.log (39693434919 / 40000000000) ≤ (480853 / 62500000) := by
  have h := checkLog_sound (w := (306565081 / 79693434919)) (n := 12)
    (lo := (7693647 / 1000000000)) (hi := (480853 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39693434919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39693434919) = 1/(39693434919 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3382 : Bounds (-480853 / 62500000) (-7693647 / 1000000000) (Real.log (39693434919 / 40000000000)) := by
  have h := reflection_log_3382_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3383_neg : (43884843 / 250000000) ≤ -Real.log (250000000000 / 297972228767) ∧
    -Real.log (250000000000 / 297972228767) ≤ (175539373 / 1000000000) := by
  have h := checkLog_sound (w := (47972228767 / 547972228767)) (n := 12)
    (lo := (43884843 / 250000000)) (hi := (175539373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((297972228767 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(297972228767 / 250000000000) = 1/(250000000000 / 297972228767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3383 : Bounds (43884843 / 250000000) (175539373 / 1000000000) (Real.log (297972228767 / 250000000000)) := by
  have h := reflection_log_3383_neg
  have he : Real.log (297972228767 / 250000000000) = -Real.log (250000000000 / 297972228767) := by
    rw [show ((297972228767 / 250000000000) : ℝ) = ((250000000000 / 297972228767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3384_neg : (21999107 / 125000000) ≤ -Real.log (250000000000 / 298107385199) ∧
    -Real.log (250000000000 / 298107385199) ≤ (175992857 / 1000000000) := by
  have h := checkLog_sound (w := (48107385199 / 548107385199)) (n := 12)
    (lo := (21999107 / 125000000)) (hi := (175992857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298107385199 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298107385199 / 250000000000) = 1/(250000000000 / 298107385199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3384 : Bounds (21999107 / 125000000) (175992857 / 1000000000) (Real.log (298107385199 / 250000000000)) := by
  have h := reflection_log_3384_neg
  have he : Real.log (298107385199 / 250000000000) = -Real.log (250000000000 / 298107385199) := by
    rw [show ((298107385199 / 250000000000) : ℝ) = ((250000000000 / 298107385199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3385_neg : (44024499 / 125000000) ≤ -Real.log (3906250000 / 5555418887) ∧
    -Real.log (3906250000 / 5555418887) ≤ (352195993 / 1000000000) := by
  have h := checkLog_sound (w := (1649168887 / 9461668887)) (n := 12)
    (lo := (44024499 / 125000000)) (hi := (352195993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5555418887 / 3906250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5555418887 / 3906250000) = 1/(3906250000 / 5555418887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3385 : Bounds (44024499 / 125000000) (352195993 / 1000000000) (Real.log (5555418887 / 3906250000)) := by
  have h := reflection_log_3385_neg
  have he : Real.log (5555418887 / 3906250000) = -Real.log (3906250000 / 5555418887) := by
    rw [show ((5555418887 / 3906250000) : ℝ) = ((3906250000 / 5555418887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3386_neg : (352402263 / 1000000000) ≤ -Real.log (250000000000 / 355620155039) ∧
    -Real.log (250000000000 / 355620155039) ≤ (44050283 / 125000000) := by
  have h := checkLog_sound (w := (105620155039 / 605620155039)) (n := 12)
    (lo := (352402263 / 1000000000)) (hi := (44050283 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355620155039 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355620155039 / 250000000000) = 1/(250000000000 / 355620155039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3386 : Bounds (352402263 / 1000000000) (44050283 / 125000000) (Real.log (355620155039 / 250000000000)) := by
  have h := reflection_log_3386_neg
  have he : Real.log (355620155039 / 250000000000) = -Real.log (250000000000 / 355620155039) := by
    rw [show ((355620155039 / 250000000000) : ℝ) = ((250000000000 / 355620155039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3387_neg : (6433701 / 40000000) ≤ -Real.log (2000 / 2349) ∧
    -Real.log (2000 / 2349) ≤ (80421263 / 500000000) := by
  have h := checkLog_sound (w := (349 / 4349)) (n := 12)
    (lo := (6433701 / 40000000)) (hi := (80421263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2349 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2349 / 2000) = 1/(2000 / 2349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3387 : Bounds (6433701 / 40000000) (80421263 / 500000000) (Real.log (2349 / 2000)) := by
  have h := reflection_log_3387_neg
  have he : Real.log (2349 / 2000) = -Real.log (2000 / 2349) := by
    rw [show ((2349 / 2000) : ℝ) = ((2000 / 2349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3388_neg : (38353203 / 200000000) ≤ -Real.log (1651 / 2000) ∧
    -Real.log (1651 / 2000) ≤ (374543 / 1953125) := by
  have h := checkLog_sound (w := (349 / 3651)) (n := 12)
    (lo := (38353203 / 200000000)) (hi := (374543 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1651) = 1/(1651 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3388 : Bounds (-374543 / 1953125) (-38353203 / 200000000) (Real.log (1651 / 2000)) := by
  have h := reflection_log_3388_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3389_neg : (43621 / 250000000) ≤ -Real.log (2000000 / 2000349) ∧
    -Real.log (2000000 / 2000349) ≤ (34897 / 200000000) := by
  have h := checkLog_sound (w := (349 / 4000349)) (n := 12)
    (lo := (43621 / 250000000)) (hi := (34897 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000349 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000349 / 2000000) = 1/(2000000 / 2000349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3389 : Bounds (43621 / 250000000) (34897 / 200000000) (Real.log (2000349 / 2000000)) := by
  have h := reflection_log_3389_neg
  have he : Real.log (2000349 / 2000000) = -Real.log (2000000 / 2000349) := by
    rw [show ((2000349 / 2000000) : ℝ) = ((2000000 / 2000349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3390_neg : (34903 / 200000000) ≤ -Real.log (1999651 / 2000000) ∧
    -Real.log (1999651 / 2000000) ≤ (43629 / 250000000) := by
  have h := checkLog_sound (w := (349 / 3999651)) (n := 12)
    (lo := (34903 / 200000000)) (hi := (43629 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999651) = 1/(1999651 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3390 : Bounds (-43629 / 250000000) (-34903 / 200000000) (Real.log (1999651 / 2000000)) := by
  have h := reflection_log_3390_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3391_neg : (20992209 / 250000000) ≤ -Real.log (200000 / 217519) ∧
    -Real.log (200000 / 217519) ≤ (83968837 / 1000000000) := by
  have h := checkLog_sound (w := (17519 / 417519)) (n := 12)
    (lo := (20992209 / 250000000)) (hi := (83968837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217519 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217519 / 200000) = 1/(200000 / 217519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3391 : Bounds (20992209 / 250000000) (83968837 / 1000000000) (Real.log (217519 / 200000)) := by
  have h := reflection_log_3391_neg
  have he : Real.log (217519 / 200000) = -Real.log (200000 / 217519) := by
    rw [show ((217519 / 200000) : ℝ) = ((200000 / 217519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
