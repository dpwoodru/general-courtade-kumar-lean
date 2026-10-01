import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10880_neg : (6777949 / 31250000) ≤ -Real.log (161003 / 200000) ∧
    -Real.log (161003 / 200000) ≤ (216894369 / 1000000000) := by
  have h := checkLog_sound (w := (38997 / 361003)) (n := 12)
    (lo := (6777949 / 31250000)) (hi := (216894369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 161003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 161003) = 1/(161003 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10880 : Bounds (-216894369 / 1000000000) (-6777949 / 31250000) (Real.log (161003 / 200000)) := by
  have h := reflection_log_10880_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10881_neg : (178897367 / 1000000000) ≤ -Real.log (500000 / 597949) ∧
    -Real.log (500000 / 597949) ≤ (22362171 / 125000000) := by
  have h := checkLog_sound (w := (97949 / 1097949)) (n := 12)
    (lo := (178897367 / 1000000000)) (hi := (22362171 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597949 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597949 / 500000) = 1/(500000 / 597949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10881 : Bounds (178897367 / 1000000000) (22362171 / 125000000) (Real.log (597949 / 500000)) := by
  have h := reflection_log_10881_neg
  have he : Real.log (597949 / 500000) = -Real.log (500000 / 597949) := by
    rw [show ((597949 / 500000) : ℝ) = ((500000 / 597949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10882_neg : (6813411 / 31250000) ≤ -Real.log (402051 / 500000) ∧
    -Real.log (402051 / 500000) ≤ (218029153 / 1000000000) := by
  have h := checkLog_sound (w := (97949 / 902051)) (n := 12)
    (lo := (6813411 / 31250000)) (hi := (218029153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 402051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 402051) = 1/(402051 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10882 : Bounds (-218029153 / 1000000000) (-6813411 / 31250000) (Real.log (402051 / 500000)) := by
  have h := reflection_log_10882_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10883_neg : (4891473 / 125000000) ≤ -Real.log (240405993399 / 250000000000) ∧
    -Real.log (240405993399 / 250000000000) ≤ (7826357 / 200000000) := by
  have h := checkLog_sound (w := (9594006601 / 490405993399)) (n := 12)
    (lo := (4891473 / 125000000)) (hi := (7826357 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240405993399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240405993399) = 1/(240405993399 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10883 : Bounds (-7826357 / 200000000) (-4891473 / 125000000) (Real.log (240405993399 / 250000000000)) := by
  have h := reflection_log_10883_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10884_neg : (7752147 / 200000000) ≤ -Real.log (38479233991 / 40000000000) ∧
    -Real.log (38479233991 / 40000000000) ≤ (1211273 / 31250000) := by
  have h := checkLog_sound (w := (1520766009 / 78479233991)) (n := 12)
    (lo := (7752147 / 200000000)) (hi := (1211273 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38479233991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38479233991) = 1/(38479233991 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10884 : Bounds (-1211273 / 31250000) (-7752147 / 200000000) (Real.log (38479233991 / 40000000000)) := by
  have h := reflection_log_10884_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10885_neg : (395028001 / 1000000000) ≤ -Real.log (25000000000 / 37110643901) ∧
    -Real.log (25000000000 / 37110643901) ≤ (197514001 / 500000000) := by
  have h := checkLog_sound (w := (12110643901 / 62110643901)) (n := 12)
    (lo := (395028001 / 1000000000)) (hi := (197514001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37110643901 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37110643901 / 25000000000) = 1/(25000000000 / 37110643901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10885 : Bounds (395028001 / 1000000000) (197514001 / 500000000) (Real.log (37110643901 / 25000000000)) := by
  have h := reflection_log_10885_neg
  have he : Real.log (37110643901 / 25000000000) = -Real.log (25000000000 / 37110643901) := by
    rw [show ((37110643901 / 25000000000) : ℝ) = ((25000000000 / 37110643901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10886_neg : (396926519 / 1000000000) ≤ -Real.log (25000000000 / 37181166071) ∧
    -Real.log (25000000000 / 37181166071) ≤ (9923163 / 25000000) := by
  have h := checkLog_sound (w := (12181166071 / 62181166071)) (n := 12)
    (lo := (396926519 / 1000000000)) (hi := (9923163 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37181166071 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37181166071 / 25000000000) = 1/(25000000000 / 37181166071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10886 : Bounds (396926519 / 1000000000) (9923163 / 25000000) (Real.log (37181166071 / 25000000000)) := by
  have h := reflection_log_10886_neg
  have he : Real.log (37181166071 / 25000000000) = -Real.log (25000000000 / 37181166071) := by
    rw [show ((37181166071 / 25000000000) : ℝ) = ((25000000000 / 37181166071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10887_neg : (800119299 / 1000000000) ≤ -Real.log (250000000000 / 556451612903) ∧
    -Real.log (250000000000 / 556451612903) ≤ (800119301 / 1000000000) := by
  have h := checkLog_sound (w := (56451612903 / 1056451612903)) (n := 12)
    (lo := (106972119 / 1000000000)) (hi := (2674303 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((556451612903 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(556451612903 / 500000000000) = 1/(250000000000 / 556451612903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10887 : Bounds (800119299 / 1000000000) (800119301 / 1000000000) (Real.log (556451612903 / 250000000000)) := by
  have h := reflection_log_10887_neg
  have he : Real.log (556451612903 / 250000000000) = -Real.log (250000000000 / 556451612903) := by
    rw [show ((556451612903 / 250000000000) : ℝ) = ((250000000000 / 556451612903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10888_neg : (20061447 / 25000000) ≤ -Real.log (500000000000 / 1115508885299) ∧
    -Real.log (500000000000 / 1115508885299) ≤ (401228941 / 500000000) := by
  have h := checkLog_sound (w := (115508885299 / 2115508885299)) (n := 12)
    (lo := (1093107 / 10000000)) (hi := (109310701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1115508885299 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1115508885299 / 1000000000000) = 1/(500000000000 / 1115508885299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10888 : Bounds (20061447 / 25000000) (401228941 / 500000000) (Real.log (1115508885299 / 500000000000)) := by
  have h := reflection_log_10888_neg
  have he : Real.log (1115508885299 / 500000000000) = -Real.log (500000000000 / 1115508885299) := by
    rw [show ((1115508885299 / 500000000000) : ℝ) = ((500000000000 / 1115508885299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10889_neg : (12941269 / 40000000) ≤ -Real.log (500 / 691) ∧
    -Real.log (500 / 691) ≤ (161765863 / 500000000) := by
  have h := checkLog_sound (w := (191 / 1191)) (n := 12)
    (lo := (12941269 / 40000000)) (hi := (161765863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((691 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(691 / 500) = 1/(500 / 691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10889 : Bounds (12941269 / 40000000) (161765863 / 500000000) (Real.log (691 / 500)) := by
  have h := reflection_log_10889_neg
  have he : Real.log (691 / 500) = -Real.log (500 / 691) := by
    rw [show ((691 / 500) : ℝ) = ((500 / 691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10890_neg : (481266821 / 1000000000) ≤ -Real.log (309 / 500) ∧
    -Real.log (309 / 500) ≤ (240633411 / 500000000) := by
  have h := checkLog_sound (w := (191 / 809)) (n := 12)
    (lo := (481266821 / 1000000000)) (hi := (240633411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 309) = 1/(309 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10890 : Bounds (-240633411 / 500000000) (-481266821 / 1000000000) (Real.log (309 / 500)) := by
  have h := reflection_log_10890_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10891_neg : (381927 / 1000000000) ≤ -Real.log (500000 / 500191) ∧
    -Real.log (500000 / 500191) ≤ (47741 / 125000000) := by
  have h := checkLog_sound (w := (191 / 1000191)) (n := 12)
    (lo := (381927 / 1000000000)) (hi := (47741 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500191 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500191 / 500000) = 1/(500000 / 500191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10891 : Bounds (381927 / 1000000000) (47741 / 125000000) (Real.log (500191 / 500000)) := by
  have h := reflection_log_10891_neg
  have he : Real.log (500191 / 500000) = -Real.log (500000 / 500191) := by
    rw [show ((500191 / 500000) : ℝ) = ((500000 / 500191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10892_neg : (47759 / 125000000) ≤ -Real.log (499809 / 500000) ∧
    -Real.log (499809 / 500000) ≤ (382073 / 1000000000) := by
  have h := checkLog_sound (w := (191 / 999809)) (n := 12)
    (lo := (47759 / 125000000)) (hi := (382073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499809) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499809) = 1/(499809 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10892 : Bounds (-382073 / 1000000000) (-47759 / 125000000) (Real.log (499809 / 500000)) := by
  have h := reflection_log_10892_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10893_neg : (44646773 / 250000000) ≤ -Real.log (1000000 / 1195527) ∧
    -Real.log (1000000 / 1195527) ≤ (178587093 / 1000000000) := by
  have h := checkLog_sound (w := (195527 / 2195527)) (n := 12)
    (lo := (44646773 / 250000000)) (hi := (178587093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1195527 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1195527 / 1000000) = 1/(1000000 / 1195527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10893 : Bounds (44646773 / 250000000) (178587093 / 1000000000) (Real.log (1195527 / 1000000)) := by
  have h := reflection_log_10893_neg
  have he : Real.log (1195527 / 1000000) = -Real.log (1000000 / 1195527) := by
    rw [show ((1195527 / 1000000) : ℝ) = ((1000000 / 1195527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10894_neg : (108783937 / 500000000) ≤ -Real.log (804473 / 1000000) ∧
    -Real.log (804473 / 1000000) ≤ (1740543 / 8000000) := by
  have h := checkLog_sound (w := (195527 / 1804473)) (n := 12)
    (lo := (108783937 / 500000000)) (hi := (1740543 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 804473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 804473) = 1/(804473 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10894 : Bounds (-1740543 / 8000000) (-108783937 / 500000000) (Real.log (804473 / 1000000)) := by
  have h := reflection_log_10894_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10895_neg : (44837829 / 250000000) ≤ -Real.log (1000000 / 1196441) ∧
    -Real.log (1000000 / 1196441) ≤ (179351317 / 1000000000) := by
  have h := checkLog_sound (w := (196441 / 2196441)) (n := 12)
    (lo := (44837829 / 250000000)) (hi := (179351317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1196441 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1196441 / 1000000) = 1/(1000000 / 1196441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10895 : Bounds (44837829 / 250000000) (179351317 / 1000000000) (Real.log (1196441 / 1000000)) := by
  have h := reflection_log_10895_neg
  have he : Real.log (1196441 / 1000000) = -Real.log (1000000 / 1196441) := by
    rw [show ((1196441 / 1000000) : ℝ) = ((1000000 / 1196441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10896_neg : (218704667 / 1000000000) ≤ -Real.log (803559 / 1000000) ∧
    -Real.log (803559 / 1000000) ≤ (54676167 / 250000000) := by
  have h := checkLog_sound (w := (196441 / 1803559)) (n := 12)
    (lo := (218704667 / 1000000000)) (hi := (54676167 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 803559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 803559) = 1/(803559 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10896 : Bounds (-54676167 / 250000000) (-218704667 / 1000000000) (Real.log (803559 / 1000000)) := by
  have h := reflection_log_10896_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10897_neg : (39353351 / 1000000000) ≤ -Real.log (961410933519 / 1000000000000) ∧
    -Real.log (961410933519 / 1000000000000) ≤ (4919169 / 125000000) := by
  have h := checkLog_sound (w := (38589066481 / 1961410933519)) (n := 12)
    (lo := (39353351 / 1000000000)) (hi := (4919169 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 961410933519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 961410933519) = 1/(961410933519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10897 : Bounds (-4919169 / 125000000) (-39353351 / 1000000000) (Real.log (961410933519 / 1000000000000)) := by
  have h := reflection_log_10897_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10898_neg : (38980781 / 1000000000) ≤ -Real.log (961769192271 / 1000000000000) ∧
    -Real.log (961769192271 / 1000000000000) ≤ (19490391 / 500000000) := by
  have h := checkLog_sound (w := (38230807729 / 1961769192271)) (n := 12)
    (lo := (38980781 / 1000000000)) (hi := (19490391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 961769192271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 961769192271) = 1/(961769192271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10898 : Bounds (-19490391 / 500000000) (-38980781 / 1000000000) (Real.log (961769192271 / 1000000000000)) := by
  have h := reflection_log_10898_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10899_neg : (198077483 / 500000000) ≤ -Real.log (500000000000 / 743049797817) ∧
    -Real.log (500000000000 / 743049797817) ≤ (396154967 / 1000000000) := by
  have h := checkLog_sound (w := (243049797817 / 1243049797817)) (n := 12)
    (lo := (198077483 / 500000000)) (hi := (396154967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((743049797817 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(743049797817 / 500000000000) = 1/(500000000000 / 743049797817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10899 : Bounds (198077483 / 500000000) (396154967 / 1000000000) (Real.log (743049797817 / 500000000000)) := by
  have h := reflection_log_10899_neg
  have he : Real.log (743049797817 / 500000000000) = -Real.log (500000000000 / 743049797817) := by
    rw [show ((743049797817 / 500000000000) : ℝ) = ((500000000000 / 743049797817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10900_neg : (24878499 / 62500000) ≤ -Real.log (10000000000 / 14889273843) ∧
    -Real.log (10000000000 / 14889273843) ≤ (79611197 / 200000000) := by
  have h := checkLog_sound (w := (4889273843 / 24889273843)) (n := 12)
    (lo := (24878499 / 62500000)) (hi := (79611197 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14889273843 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14889273843 / 10000000000) = 1/(10000000000 / 14889273843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10900 : Bounds (24878499 / 62500000) (79611197 / 200000000) (Real.log (14889273843 / 10000000000)) := by
  have h := reflection_log_10900_neg
  have he : Real.log (14889273843 / 10000000000) = -Real.log (10000000000 / 14889273843) := by
    rw [show ((14889273843 / 10000000000) : ℝ) = ((10000000000 / 14889273843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10901_neg : (20061447 / 25000000) ≤ -Real.log (250000000000 / 557754442649) ∧
    -Real.log (250000000000 / 557754442649) ≤ (401228941 / 500000000) := by
  have h := checkLog_sound (w := (57754442649 / 1057754442649)) (n := 12)
    (lo := (1093107 / 10000000)) (hi := (109310701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((557754442649 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(557754442649 / 500000000000) = 1/(250000000000 / 557754442649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10901 : Bounds (20061447 / 25000000) (401228941 / 500000000) (Real.log (557754442649 / 250000000000)) := by
  have h := reflection_log_10901_neg
  have he : Real.log (557754442649 / 250000000000) = -Real.log (250000000000 / 557754442649) := by
    rw [show ((557754442649 / 250000000000) : ℝ) = ((250000000000 / 557754442649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10902_neg : (402399273 / 500000000) ≤ -Real.log (500000000000 / 1118122977347) ∧
    -Real.log (500000000000 / 1118122977347) ≤ (201199637 / 250000000) := by
  have h := checkLog_sound (w := (118122977347 / 2118122977347)) (n := 12)
    (lo := (55825683 / 500000000)) (hi := (111651367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1118122977347 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1118122977347 / 1000000000000) = 1/(500000000000 / 1118122977347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10902 : Bounds (402399273 / 500000000) (201199637 / 250000000) (Real.log (1118122977347 / 500000000000)) := by
  have h := reflection_log_10902_neg
  have he : Real.log (1118122977347 / 500000000000) = -Real.log (500000000000 / 1118122977347) := by
    rw [show ((1118122977347 / 500000000000) : ℝ) = ((500000000000 / 1118122977347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10903_neg : (81063763 / 250000000) ≤ -Real.log (1000 / 1383) ∧
    -Real.log (1000 / 1383) ≤ (324255053 / 1000000000) := by
  have h := checkLog_sound (w := (383 / 2383)) (n := 12)
    (lo := (81063763 / 250000000)) (hi := (324255053 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1383 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1383 / 1000) = 1/(1000 / 1383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10903 : Bounds (81063763 / 250000000) (324255053 / 1000000000) (Real.log (1383 / 1000)) := by
  have h := reflection_log_10903_neg
  have he : Real.log (1383 / 1000) = -Real.log (1000 / 1383) := by
    rw [show ((1383 / 1000) : ℝ) = ((1000 / 1383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10904_neg : (96577251 / 200000000) ≤ -Real.log (617 / 1000) ∧
    -Real.log (617 / 1000) ≤ (30180391 / 62500000) := by
  have h := checkLog_sound (w := (383 / 1617)) (n := 12)
    (lo := (96577251 / 200000000)) (hi := (30180391 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 617) = 1/(617 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10904 : Bounds (-30180391 / 62500000) (-96577251 / 200000000) (Real.log (617 / 1000)) := by
  have h := reflection_log_10904_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10905_neg : (191463 / 500000000) ≤ -Real.log (1000000 / 1000383) ∧
    -Real.log (1000000 / 1000383) ≤ (382927 / 1000000000) := by
  have h := checkLog_sound (w := (383 / 2000383)) (n := 12)
    (lo := (191463 / 500000000)) (hi := (382927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000383 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000383 / 1000000) = 1/(1000000 / 1000383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10905 : Bounds (191463 / 500000000) (382927 / 1000000000) (Real.log (1000383 / 1000000)) := by
  have h := reflection_log_10905_neg
  have he : Real.log (1000383 / 1000000) = -Real.log (1000000 / 1000383) := by
    rw [show ((1000383 / 1000000) : ℝ) = ((1000000 / 1000383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10906_neg : (383073 / 1000000000) ≤ -Real.log (999617 / 1000000) ∧
    -Real.log (999617 / 1000000) ≤ (191537 / 500000000) := by
  have h := checkLog_sound (w := (383 / 1999617)) (n := 12)
    (lo := (383073 / 1000000000)) (hi := (191537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999617) = 1/(999617 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10906 : Bounds (-191537 / 500000000) (-383073 / 1000000000) (Real.log (999617 / 1000000)) := by
  have h := reflection_log_10906_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10907_neg : (89520173 / 500000000) ≤ -Real.log (1000000 / 1196069) ∧
    -Real.log (1000000 / 1196069) ≤ (179040347 / 1000000000) := by
  have h := checkLog_sound (w := (196069 / 2196069)) (n := 12)
    (lo := (89520173 / 500000000)) (hi := (179040347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1196069 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1196069 / 1000000) = 1/(1000000 / 1196069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10907 : Bounds (89520173 / 500000000) (179040347 / 1000000000) (Real.log (1196069 / 1000000)) := by
  have h := reflection_log_10907_neg
  have he : Real.log (1196069 / 1000000) = -Real.log (1000000 / 1196069) := by
    rw [show ((1196069 / 1000000) : ℝ) = ((1000000 / 1196069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10908_neg : (109120917 / 500000000) ≤ -Real.log (803931 / 1000000) ∧
    -Real.log (803931 / 1000000) ≤ (43648367 / 200000000) := by
  have h := checkLog_sound (w := (196069 / 1803931)) (n := 12)
    (lo := (109120917 / 500000000)) (hi := (43648367 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 803931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 803931) = 1/(803931 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10908 : Bounds (-43648367 / 200000000) (-109120917 / 500000000) (Real.log (803931 / 1000000)) := by
  have h := reflection_log_10908_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10909_neg : (179805059 / 1000000000) ≤ -Real.log (125000 / 149623) ∧
    -Real.log (125000 / 149623) ≤ (8990253 / 50000000) := by
  have h := checkLog_sound (w := (24623 / 274623)) (n := 12)
    (lo := (179805059 / 1000000000)) (hi := (8990253 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149623 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149623 / 125000) = 1/(125000 / 149623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10909 : Bounds (179805059 / 1000000000) (8990253 / 50000000) (Real.log (149623 / 125000)) := by
  have h := reflection_log_10909_neg
  have he : Real.log (149623 / 125000) = -Real.log (125000 / 149623) := by
    rw [show ((149623 / 125000) : ℝ) = ((125000 / 149623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10910_neg : (219380639 / 1000000000) ≤ -Real.log (100377 / 125000) ∧
    -Real.log (100377 / 125000) ≤ (1371129 / 6250000) := by
  have h := checkLog_sound (w := (24623 / 225377)) (n := 12)
    (lo := (219380639 / 1000000000)) (hi := (1371129 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 100377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 100377) = 1/(100377 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10910 : Bounds (-1371129 / 6250000) (-219380639 / 1000000000) (Real.log (100377 / 125000)) := by
  have h := reflection_log_10910_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10911_neg : (1978779 / 50000000) ≤ -Real.log (15018707871 / 15625000000) ∧
    -Real.log (15018707871 / 15625000000) ≤ (39575581 / 1000000000) := by
  have h := checkLog_sound (w := (606292129 / 30643707871)) (n := 12)
    (lo := (1978779 / 50000000)) (hi := (39575581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15018707871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15018707871) = 1/(15018707871 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10911 : Bounds (-39575581 / 1000000000) (-1978779 / 50000000) (Real.log (15018707871 / 15625000000)) := by
  have h := reflection_log_10911_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10912_neg : (2450093 / 62500000) ≤ -Real.log (961556947239 / 1000000000000) ∧
    -Real.log (961556947239 / 1000000000000) ≤ (39201489 / 1000000000) := by
  have h := checkLog_sound (w := (38443052761 / 1961556947239)) (n := 12)
    (lo := (2450093 / 62500000)) (hi := (39201489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 961556947239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 961556947239) = 1/(961556947239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10912 : Bounds (-39201489 / 1000000000) (-2450093 / 62500000) (Real.log (961556947239 / 1000000000000)) := by
  have h := reflection_log_10912_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10913_neg : (19864109 / 50000000) ≤ -Real.log (31250000000 / 46492990381) ∧
    -Real.log (31250000000 / 46492990381) ≤ (397282181 / 1000000000) := by
  have h := checkLog_sound (w := (15242990381 / 77742990381)) (n := 12)
    (lo := (19864109 / 50000000)) (hi := (397282181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46492990381 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46492990381 / 31250000000) = 1/(31250000000 / 46492990381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10913 : Bounds (19864109 / 50000000) (397282181 / 1000000000) (Real.log (46492990381 / 31250000000)) := by
  have h := reflection_log_10913_neg
  have he : Real.log (46492990381 / 31250000000) = -Real.log (31250000000 / 46492990381) := by
    rw [show ((46492990381 / 31250000000) : ℝ) = ((31250000000 / 46492990381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10914_neg : (399185699 / 1000000000) ≤ -Real.log (500000000000 / 745305199399) ∧
    -Real.log (500000000000 / 745305199399) ≤ (3991857 / 10000000) := by
  have h := checkLog_sound (w := (245305199399 / 1245305199399)) (n := 12)
    (lo := (399185699 / 1000000000)) (hi := (3991857 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((745305199399 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(745305199399 / 500000000000) = 1/(500000000000 / 745305199399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10914 : Bounds (399185699 / 1000000000) (3991857 / 10000000) (Real.log (745305199399 / 500000000000)) := by
  have h := reflection_log_10914_neg
  have he : Real.log (745305199399 / 500000000000) = -Real.log (500000000000 / 745305199399) := by
    rw [show ((745305199399 / 500000000000) : ℝ) = ((500000000000 / 745305199399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10915_neg : (402399273 / 500000000) ≤ -Real.log (250000000000 / 559061488673) ∧
    -Real.log (250000000000 / 559061488673) ≤ (201199637 / 250000000) := by
  have h := checkLog_sound (w := (59061488673 / 1059061488673)) (n := 12)
    (lo := (55825683 / 500000000)) (hi := (111651367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((559061488673 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(559061488673 / 500000000000) = 1/(250000000000 / 559061488673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10915 : Bounds (402399273 / 500000000) (201199637 / 250000000) (Real.log (559061488673 / 250000000000)) := by
  have h := reflection_log_10915_neg
  have he : Real.log (559061488673 / 250000000000) = -Real.log (250000000000 / 559061488673) := by
    rw [show ((559061488673 / 250000000000) : ℝ) = ((250000000000 / 559061488673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10916_neg : (807141307 / 1000000000) ≤ -Real.log (10000000000 / 22414910859) ∧
    -Real.log (10000000000 / 22414910859) ≤ (807141309 / 1000000000) := by
  have h := checkLog_sound (w := (2414910859 / 42414910859)) (n := 12)
    (lo := (113994127 / 1000000000)) (hi := (7124633 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((22414910859 / 20000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(22414910859 / 20000000000) = 1/(10000000000 / 22414910859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10916 : Bounds (807141307 / 1000000000) (807141309 / 1000000000) (Real.log (22414910859 / 10000000000)) := by
  have h := reflection_log_10916_neg
  have he : Real.log (22414910859 / 10000000000) = -Real.log (10000000000 / 22414910859) := by
    rw [show ((22414910859 / 10000000000) : ℝ) = ((10000000000 / 22414910859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10917_neg : (324977857 / 1000000000) ≤ -Real.log (125 / 173) ∧
    -Real.log (125 / 173) ≤ (162488929 / 500000000) := by
  have h := checkLog_sound (w := (24 / 149)) (n := 12)
    (lo := (324977857 / 1000000000)) (hi := (162488929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173 / 125) = 1/(125 / 173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10917 : Bounds (324977857 / 1000000000) (162488929 / 500000000) (Real.log (173 / 125)) := by
  have h := reflection_log_10917_neg
  have he : Real.log (173 / 125) = -Real.log (125 / 173) := by
    rw [show ((173 / 125) : ℝ) = ((125 / 173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10918_neg : (96901663 / 200000000) ≤ -Real.log (77 / 125) ∧
    -Real.log (77 / 125) ≤ (121127079 / 250000000) := by
  have h := checkLog_sound (w := (24 / 101)) (n := 12)
    (lo := (96901663 / 200000000)) (hi := (121127079 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 77) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 77) = 1/(77 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10918 : Bounds (-121127079 / 250000000) (-96901663 / 200000000) (Real.log (77 / 125)) := by
  have h := reflection_log_10918_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10919_neg : (191963 / 500000000) ≤ -Real.log (15625 / 15631) ∧
    -Real.log (15625 / 15631) ≤ (383927 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 15628)) (n := 12)
    (lo := (191963 / 500000000)) (hi := (383927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15631 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15631 / 15625) = 1/(15625 / 15631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10919 : Bounds (191963 / 500000000) (383927 / 1000000000) (Real.log (15631 / 15625)) := by
  have h := reflection_log_10919_neg
  have he : Real.log (15631 / 15625) = -Real.log (15625 / 15631) := by
    rw [show ((15631 / 15625) : ℝ) = ((15625 / 15631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10920_neg : (384073 / 1000000000) ≤ -Real.log (15619 / 15625) ∧
    -Real.log (15619 / 15625) ≤ (192037 / 500000000) := by
  have h := checkLog_sound (w := (3 / 15622)) (n := 12)
    (lo := (384073 / 1000000000)) (hi := (192037 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 15619) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 15619) = 1/(15619 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10920 : Bounds (-192037 / 500000000) (-384073 / 1000000000) (Real.log (15619 / 15625)) := by
  have h := reflection_log_10920_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10921_neg : (89746697 / 500000000) ≤ -Real.log (1000000 / 1196611) ∧
    -Real.log (1000000 / 1196611) ≤ (35898679 / 200000000) := by
  have h := checkLog_sound (w := (196611 / 2196611)) (n := 12)
    (lo := (89746697 / 500000000)) (hi := (35898679 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1196611 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1196611 / 1000000) = 1/(1000000 / 1196611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10921 : Bounds (89746697 / 500000000) (35898679 / 200000000) (Real.log (1196611 / 1000000)) := by
  have h := reflection_log_10921_neg
  have he : Real.log (1196611 / 1000000) = -Real.log (1000000 / 1196611) := by
    rw [show ((1196611 / 1000000) : ℝ) = ((1000000 / 1196611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10922_neg : (27364531 / 125000000) ≤ -Real.log (803389 / 1000000) ∧
    -Real.log (803389 / 1000000) ≤ (218916249 / 1000000000) := by
  have h := checkLog_sound (w := (196611 / 1803389)) (n := 12)
    (lo := (27364531 / 125000000)) (hi := (218916249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 803389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 803389) = 1/(803389 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10922 : Bounds (-218916249 / 1000000000) (-27364531 / 125000000) (Real.log (803389 / 1000000)) := by
  have h := reflection_log_10922_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10923_neg : (180258597 / 1000000000) ≤ -Real.log (1000000 / 1197527) ∧
    -Real.log (1000000 / 1197527) ≤ (90129299 / 500000000) := by
  have h := checkLog_sound (w := (197527 / 2197527)) (n := 12)
    (lo := (180258597 / 1000000000)) (hi := (90129299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1197527 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1197527 / 1000000) = 1/(1000000 / 1197527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10923 : Bounds (180258597 / 1000000000) (90129299 / 500000000) (Real.log (1197527 / 1000000)) := by
  have h := reflection_log_10923_neg
  have he : Real.log (1197527 / 1000000) = -Real.log (1000000 / 1197527) := by
    rw [show ((1197527 / 1000000) : ℝ) = ((1000000 / 1197527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10924_neg : (220057069 / 1000000000) ≤ -Real.log (802473 / 1000000) ∧
    -Real.log (802473 / 1000000) ≤ (22005707 / 100000000) := by
  have h := checkLog_sound (w := (197527 / 1802473)) (n := 12)
    (lo := (220057069 / 1000000000)) (hi := (22005707 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 802473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 802473) = 1/(802473 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10924 : Bounds (-22005707 / 100000000) (-220057069 / 1000000000) (Real.log (802473 / 1000000)) := by
  have h := reflection_log_10924_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10925_neg : (4974809 / 125000000) ≤ -Real.log (960983084271 / 1000000000000) ∧
    -Real.log (960983084271 / 1000000000000) ≤ (39798473 / 1000000000) := by
  have h := checkLog_sound (w := (39016915729 / 1960983084271)) (n := 12)
    (lo := (4974809 / 125000000)) (hi := (39798473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 960983084271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 960983084271) = 1/(960983084271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10925 : Bounds (-39798473 / 1000000000) (-4974809 / 125000000) (Real.log (960983084271 / 1000000000000)) := by
  have h := reflection_log_10925_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10926_neg : (19711427 / 500000000) ≤ -Real.log (961344114679 / 1000000000000) ∧
    -Real.log (961344114679 / 1000000000000) ≤ (7884571 / 200000000) := by
  have h := checkLog_sound (w := (38655885321 / 1961344114679)) (n := 12)
    (lo := (19711427 / 500000000)) (hi := (7884571 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 961344114679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 961344114679) = 1/(961344114679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10926 : Bounds (-7884571 / 200000000) (-19711427 / 500000000) (Real.log (961344114679 / 1000000000000)) := by
  have h := reflection_log_10926_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10927_neg : (398409643 / 1000000000) ≤ -Real.log (500000000000 / 744727025139) ∧
    -Real.log (500000000000 / 744727025139) ≤ (99602411 / 250000000) := by
  have h := checkLog_sound (w := (244727025139 / 1244727025139)) (n := 12)
    (lo := (398409643 / 1000000000)) (hi := (99602411 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((744727025139 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(744727025139 / 500000000000) = 1/(500000000000 / 744727025139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10927 : Bounds (398409643 / 1000000000) (99602411 / 250000000) (Real.log (744727025139 / 500000000000)) := by
  have h := reflection_log_10927_neg
  have he : Real.log (744727025139 / 500000000000) = -Real.log (500000000000 / 744727025139) := by
    rw [show ((744727025139 / 500000000000) : ℝ) = ((500000000000 / 744727025139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10928_neg : (200157833 / 500000000) ≤ -Real.log (500000000000 / 746147845473) ∧
    -Real.log (500000000000 / 746147845473) ≤ (400315667 / 1000000000) := by
  have h := checkLog_sound (w := (246147845473 / 1246147845473)) (n := 12)
    (lo := (200157833 / 500000000)) (hi := (400315667 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746147845473 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746147845473 / 500000000000) = 1/(500000000000 / 746147845473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10928 : Bounds (200157833 / 500000000) (400315667 / 1000000000) (Real.log (746147845473 / 500000000000)) := by
  have h := reflection_log_10928_neg
  have he : Real.log (746147845473 / 500000000000) = -Real.log (500000000000 / 746147845473) := by
    rw [show ((746147845473 / 500000000000) : ℝ) = ((500000000000 / 746147845473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10929_neg : (807141307 / 1000000000) ≤ -Real.log (500000000000 / 1120745542949) ∧
    -Real.log (500000000000 / 1120745542949) ≤ (807141309 / 1000000000) := by
  have h := checkLog_sound (w := (120745542949 / 2120745542949)) (n := 12)
    (lo := (113994127 / 1000000000)) (hi := (7124633 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1120745542949 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1120745542949 / 1000000000000) = 1/(500000000000 / 1120745542949) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10929 : Bounds (807141307 / 1000000000) (807141309 / 1000000000) (Real.log (1120745542949 / 500000000000)) := by
  have h := reflection_log_10929_neg
  have he : Real.log (1120745542949 / 500000000000) = -Real.log (500000000000 / 1120745542949) := by
    rw [show ((1120745542949 / 500000000000) : ℝ) = ((500000000000 / 1120745542949) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10930_neg : (202371543 / 250000000) ≤ -Real.log (500000000000 / 1123376623377) ∧
    -Real.log (500000000000 / 1123376623377) ≤ (404743087 / 500000000) := by
  have h := checkLog_sound (w := (123376623377 / 2123376623377)) (n := 12)
    (lo := (7271187 / 62500000)) (hi := (116338993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1123376623377 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1123376623377 / 1000000000000) = 1/(500000000000 / 1123376623377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10930 : Bounds (202371543 / 250000000) (404743087 / 500000000) (Real.log (1123376623377 / 500000000000)) := by
  have h := reflection_log_10930_neg
  have he : Real.log (1123376623377 / 500000000000) = -Real.log (500000000000 / 1123376623377) := by
    rw [show ((1123376623377 / 500000000000) : ℝ) = ((500000000000 / 1123376623377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10931_neg : (325700139 / 1000000000) ≤ -Real.log (200 / 277) ∧
    -Real.log (200 / 277) ≤ (16285007 / 50000000) := by
  have h := checkLog_sound (w := (77 / 477)) (n := 12)
    (lo := (325700139 / 1000000000)) (hi := (16285007 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((277 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(277 / 200) = 1/(200 / 277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10931 : Bounds (325700139 / 1000000000) (16285007 / 50000000) (Real.log (277 / 200)) := by
  have h := reflection_log_10931_neg
  have he : Real.log (277 / 200) = -Real.log (200 / 277) := by
    rw [show ((277 / 200) : ℝ) = ((200 / 277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10932_neg : (486133011 / 1000000000) ≤ -Real.log (123 / 200) ∧
    -Real.log (123 / 200) ≤ (121533253 / 250000000) := by
  have h := checkLog_sound (w := (77 / 323)) (n := 12)
    (lo := (486133011 / 1000000000)) (hi := (121533253 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 123) = 1/(123 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10932 : Bounds (-121533253 / 250000000) (-486133011 / 1000000000) (Real.log (123 / 200)) := by
  have h := reflection_log_10932_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10933_neg : (15397 / 40000000) ≤ -Real.log (200000 / 200077) ∧
    -Real.log (200000 / 200077) ≤ (192463 / 500000000) := by
  have h := checkLog_sound (w := (77 / 400077)) (n := 12)
    (lo := (15397 / 40000000)) (hi := (192463 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200077 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200077 / 200000) = 1/(200000 / 200077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10933 : Bounds (15397 / 40000000) (192463 / 500000000) (Real.log (200077 / 200000)) := by
  have h := reflection_log_10933_neg
  have he : Real.log (200077 / 200000) = -Real.log (200000 / 200077) := by
    rw [show ((200077 / 200000) : ℝ) = ((200000 / 200077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10934_neg : (192537 / 500000000) ≤ -Real.log (199923 / 200000) ∧
    -Real.log (199923 / 200000) ≤ (15403 / 40000000) := by
  have h := checkLog_sound (w := (77 / 399923)) (n := 12)
    (lo := (192537 / 500000000)) (hi := (15403 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199923) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199923) = 1/(199923 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10934 : Bounds (-15403 / 40000000) (-192537 / 500000000) (Real.log (199923 / 200000)) := by
  have h := reflection_log_10934_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10935_neg : (179947073 / 1000000000) ≤ -Real.log (500000 / 598577) ∧
    -Real.log (500000 / 598577) ≤ (89973537 / 500000000) := by
  have h := checkLog_sound (w := (98577 / 1098577)) (n := 12)
    (lo := (179947073 / 1000000000)) (hi := (89973537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598577 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598577 / 500000) = 1/(500000 / 598577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10935 : Bounds (179947073 / 1000000000) (89973537 / 500000000) (Real.log (598577 / 500000)) := by
  have h := reflection_log_10935_neg
  have he : Real.log (598577 / 500000) = -Real.log (500000 / 598577) := by
    rw [show ((598577 / 500000) : ℝ) = ((500000 / 598577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10936_neg : (54898091 / 250000000) ≤ -Real.log (401423 / 500000) ∧
    -Real.log (401423 / 500000) ≤ (43918473 / 200000000) := by
  have h := checkLog_sound (w := (98577 / 901423)) (n := 12)
    (lo := (54898091 / 250000000)) (hi := (43918473 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 401423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 401423) = 1/(401423 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10936 : Bounds (-43918473 / 200000000) (-54898091 / 250000000) (Real.log (401423 / 500000)) := by
  have h := reflection_log_10936_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10937_neg : (180712763 / 1000000000) ≤ -Real.log (1000000 / 1198071) ∧
    -Real.log (1000000 / 1198071) ≤ (45178191 / 250000000) := by
  have h := checkLog_sound (w := (198071 / 2198071)) (n := 12)
    (lo := (180712763 / 1000000000)) (hi := (45178191 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1198071 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1198071 / 1000000) = 1/(1000000 / 1198071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10937 : Bounds (180712763 / 1000000000) (45178191 / 250000000) (Real.log (1198071 / 1000000)) := by
  have h := reflection_log_10937_neg
  have he : Real.log (1198071 / 1000000) = -Real.log (1000000 / 1198071) := by
    rw [show ((1198071 / 1000000) : ℝ) = ((1000000 / 1198071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10938_neg : (220735203 / 1000000000) ≤ -Real.log (801929 / 1000000) ∧
    -Real.log (801929 / 1000000) ≤ (55183801 / 250000000) := by
  have h := checkLog_sound (w := (198071 / 1801929)) (n := 12)
    (lo := (220735203 / 1000000000)) (hi := (55183801 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 801929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 801929) = 1/(801929 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10938 : Bounds (-55183801 / 250000000) (-220735203 / 1000000000) (Real.log (801929 / 1000000)) := by
  have h := reflection_log_10938_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10939_neg : (1000561 / 25000000) ≤ -Real.log (960767878959 / 1000000000000) ∧
    -Real.log (960767878959 / 1000000000000) ≤ (40022441 / 1000000000) := by
  have h := checkLog_sound (w := (39232121041 / 1960767878959)) (n := 12)
    (lo := (1000561 / 25000000)) (hi := (40022441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 960767878959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 960767878959) = 1/(960767878959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10939 : Bounds (-40022441 / 1000000000) (-1000561 / 25000000) (Real.log (960767878959 / 1000000000000)) := by
  have h := reflection_log_10939_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10940_neg : (3964529 / 100000000) ≤ -Real.log (240282575071 / 250000000000) ∧
    -Real.log (240282575071 / 250000000000) ≤ (39645291 / 1000000000) := by
  have h := checkLog_sound (w := (9717424929 / 490282575071)) (n := 12)
    (lo := (3964529 / 100000000)) (hi := (39645291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 240282575071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 240282575071) = 1/(240282575071 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10940 : Bounds (-39645291 / 1000000000) (-3964529 / 100000000) (Real.log (240282575071 / 250000000000)) := by
  have h := reflection_log_10940_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10941_neg : (399539437 / 1000000000) ≤ -Real.log (250000000000 / 372784444339) ∧
    -Real.log (250000000000 / 372784444339) ≤ (199769719 / 500000000) := by
  have h := checkLog_sound (w := (122784444339 / 622784444339)) (n := 12)
    (lo := (399539437 / 1000000000)) (hi := (199769719 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((372784444339 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(372784444339 / 250000000000) = 1/(250000000000 / 372784444339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10941 : Bounds (399539437 / 1000000000) (199769719 / 500000000) (Real.log (372784444339 / 250000000000)) := by
  have h := reflection_log_10941_neg
  have he : Real.log (372784444339 / 250000000000) = -Real.log (250000000000 / 372784444339) := by
    rw [show ((372784444339 / 250000000000) : ℝ) = ((250000000000 / 372784444339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10942_neg : (401447967 / 1000000000) ≤ -Real.log (500000000000 / 746993187677) ∧
    -Real.log (500000000000 / 746993187677) ≤ (12545249 / 31250000) := by
  have h := checkLog_sound (w := (246993187677 / 1246993187677)) (n := 12)
    (lo := (401447967 / 1000000000)) (hi := (12545249 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746993187677 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(746993187677 / 500000000000) = 1/(500000000000 / 746993187677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10942 : Bounds (401447967 / 1000000000) (12545249 / 31250000) (Real.log (746993187677 / 500000000000)) := by
  have h := reflection_log_10942_neg
  have he : Real.log (746993187677 / 500000000000) = -Real.log (500000000000 / 746993187677) := by
    rw [show ((746993187677 / 500000000000) : ℝ) = ((500000000000 / 746993187677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10943_neg : (202371543 / 250000000) ≤ -Real.log (31250000000 / 70211038961) ∧
    -Real.log (31250000000 / 70211038961) ≤ (404743087 / 500000000) := by
  have h := checkLog_sound (w := (7711038961 / 132711038961)) (n := 12)
    (lo := (7271187 / 62500000)) (hi := (116338993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70211038961 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(70211038961 / 62500000000) = 1/(31250000000 / 70211038961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10943 : Bounds (202371543 / 250000000) (404743087 / 500000000) (Real.log (70211038961 / 31250000000)) := by
  have h := reflection_log_10943_neg
  have he : Real.log (70211038961 / 31250000000) = -Real.log (31250000000 / 70211038961) := by
    rw [show ((70211038961 / 31250000000) : ℝ) = ((31250000000 / 70211038961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
