import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10112_neg : (674455047 / 1000000000) ≤ -Real.log (250000000000 / 490740740741) ∧
    -Real.log (250000000000 / 490740740741) ≤ (84306881 / 125000000) := by
  have h := checkLog_sound (w := (240740740741 / 740740740741)) (n := 12)
    (lo := (674455047 / 1000000000)) (hi := (84306881 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((490740740741 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(490740740741 / 250000000000) = 1/(250000000000 / 490740740741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10112 : Bounds (674455047 / 1000000000) (84306881 / 125000000) (Real.log (490740740741 / 250000000000)) := by
  have h := reflection_log_10112_neg
  have he : Real.log (490740740741 / 250000000000) = -Real.log (250000000000 / 490740740741) := by
    rw [show ((490740740741 / 250000000000) : ℝ) = ((250000000000 / 490740740741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10113_neg : (282166891 / 1000000000) ≤ -Real.log (500 / 663) ∧
    -Real.log (500 / 663) ≤ (70541723 / 250000000) := by
  have h := checkLog_sound (w := (163 / 1163)) (n := 12)
    (lo := (282166891 / 1000000000)) (hi := (70541723 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((663 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(663 / 500) = 1/(500 / 663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10113 : Bounds (282166891 / 1000000000) (70541723 / 250000000) (Real.log (663 / 500)) := by
  have h := reflection_log_10113_neg
  have he : Real.log (663 / 500) = -Real.log (500 / 663) := by
    rw [show ((663 / 500) : ℝ) = ((500 / 663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10114_neg : (24657823 / 62500000) ≤ -Real.log (337 / 500) ∧
    -Real.log (337 / 500) ≤ (394525169 / 1000000000) := by
  have h := checkLog_sound (w := (163 / 837)) (n := 12)
    (lo := (24657823 / 62500000)) (hi := (394525169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 337) = 1/(337 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10114 : Bounds (-394525169 / 1000000000) (-24657823 / 62500000) (Real.log (337 / 500)) := by
  have h := reflection_log_10114_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10115_neg : (162973 / 500000000) ≤ -Real.log (500000 / 500163) ∧
    -Real.log (500000 / 500163) ≤ (325947 / 1000000000) := by
  have h := checkLog_sound (w := (163 / 1000163)) (n := 12)
    (lo := (162973 / 500000000)) (hi := (325947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500163 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500163 / 500000) = 1/(500000 / 500163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10115 : Bounds (162973 / 500000000) (325947 / 1000000000) (Real.log (500163 / 500000)) := by
  have h := reflection_log_10115_neg
  have he : Real.log (500163 / 500000) = -Real.log (500000 / 500163) := by
    rw [show ((500163 / 500000) : ℝ) = ((500000 / 500163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10116_neg : (326053 / 1000000000) ≤ -Real.log (499837 / 500000) ∧
    -Real.log (499837 / 500000) ≤ (163027 / 500000000) := by
  have h := checkLog_sound (w := (163 / 999837)) (n := 12)
    (lo := (326053 / 1000000000)) (hi := (163027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499837) = 1/(499837 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10116 : Bounds (-163027 / 500000000) (-326053 / 1000000000) (Real.log (499837 / 500000)) := by
  have h := reflection_log_10116_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10117_neg : (153181067 / 1000000000) ≤ -Real.log (31250 / 36423) ∧
    -Real.log (31250 / 36423) ≤ (38295267 / 250000000) := by
  have h := checkLog_sound (w := (5173 / 67673)) (n := 12)
    (lo := (153181067 / 1000000000)) (hi := (38295267 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36423 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36423 / 31250) = 1/(31250 / 36423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10117 : Bounds (153181067 / 1000000000) (38295267 / 250000000) (Real.log (36423 / 31250)) := by
  have h := reflection_log_10117_neg
  have he : Real.log (36423 / 31250) = -Real.log (31250 / 36423) := by
    rw [show ((36423 / 31250) : ℝ) = ((31250 / 36423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10118_neg : (45241419 / 250000000) ≤ -Real.log (26077 / 31250) ∧
    -Real.log (26077 / 31250) ≤ (180965677 / 1000000000) := by
  have h := checkLog_sound (w := (5173 / 57327)) (n := 12)
    (lo := (45241419 / 250000000)) (hi := (180965677 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 26077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 26077) = 1/(26077 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10118 : Bounds (-180965677 / 1000000000) (-45241419 / 250000000) (Real.log (26077 / 31250)) := by
  have h := reflection_log_10118_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10119_neg : (153910079 / 1000000000) ≤ -Real.log (500000 / 583193) ∧
    -Real.log (500000 / 583193) ≤ (480969 / 3125000) := by
  have h := checkLog_sound (w := (83193 / 1083193)) (n := 12)
    (lo := (153910079 / 1000000000)) (hi := (480969 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583193 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583193 / 500000) = 1/(500000 / 583193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10119 : Bounds (153910079 / 1000000000) (480969 / 3125000) (Real.log (583193 / 500000)) := by
  have h := reflection_log_10119_neg
  have he : Real.log (583193 / 500000) = -Real.log (500000 / 583193) := by
    rw [show ((583193 / 500000) : ℝ) = ((500000 / 583193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10120_neg : (181984813 / 1000000000) ≤ -Real.log (416807 / 500000) ∧
    -Real.log (416807 / 500000) ≤ (90992407 / 500000000) := by
  have h := checkLog_sound (w := (83193 / 916807)) (n := 12)
    (lo := (181984813 / 1000000000)) (hi := (90992407 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 416807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 416807) = 1/(416807 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10120 : Bounds (-90992407 / 500000000) (-181984813 / 1000000000) (Real.log (416807 / 500000)) := by
  have h := reflection_log_10120_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10121_neg : (14037367 / 500000000) ≤ -Real.log (243078924751 / 250000000000) ∧
    -Real.log (243078924751 / 250000000000) ≤ (5614947 / 200000000) := by
  have h := checkLog_sound (w := (6921075249 / 493078924751)) (n := 12)
    (lo := (14037367 / 500000000)) (hi := (5614947 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243078924751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243078924751) = 1/(243078924751 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10121 : Bounds (-5614947 / 200000000) (-14037367 / 500000000) (Real.log (243078924751 / 250000000000)) := by
  have h := reflection_log_10121_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10122_neg : (27784609 / 1000000000) ≤ -Real.log (949802571 / 976562500) ∧
    -Real.log (949802571 / 976562500) ≤ (2778461 / 100000000) := by
  have h := checkLog_sound (w := (26759929 / 1926365071)) (n := 12)
    (lo := (27784609 / 1000000000)) (hi := (2778461 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 949802571) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 949802571) = 1/(949802571 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10122 : Bounds (-2778461 / 100000000) (-27784609 / 1000000000) (Real.log (949802571 / 976562500)) := by
  have h := reflection_log_10122_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10123_neg : (334146743 / 1000000000) ≤ -Real.log (250000000000 / 349187023047) ∧
    -Real.log (250000000000 / 349187023047) ≤ (41768343 / 125000000) := by
  have h := checkLog_sound (w := (99187023047 / 599187023047)) (n := 12)
    (lo := (334146743 / 1000000000)) (hi := (41768343 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349187023047 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(349187023047 / 250000000000) = 1/(250000000000 / 349187023047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10123 : Bounds (334146743 / 1000000000) (41768343 / 125000000) (Real.log (349187023047 / 250000000000)) := by
  have h := reflection_log_10123_neg
  have he : Real.log (349187023047 / 250000000000) = -Real.log (250000000000 / 349187023047) := by
    rw [show ((349187023047 / 250000000000) : ℝ) = ((250000000000 / 349187023047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10124_neg : (83973723 / 250000000) ≤ -Real.log (125000000000 / 174898994019) ∧
    -Real.log (125000000000 / 174898994019) ≤ (335894893 / 1000000000) := by
  have h := checkLog_sound (w := (49898994019 / 299898994019)) (n := 12)
    (lo := (83973723 / 250000000)) (hi := (335894893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((174898994019 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(174898994019 / 125000000000) = 1/(125000000000 / 174898994019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10124 : Bounds (83973723 / 250000000) (335894893 / 1000000000) (Real.log (174898994019 / 125000000000)) := by
  have h := reflection_log_10124_neg
  have he : Real.log (174898994019 / 125000000000) = -Real.log (125000000000 / 174898994019) := by
    rw [show ((174898994019 / 125000000000) : ℝ) = ((125000000000 / 174898994019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10125_neg : (674455047 / 1000000000) ≤ -Real.log (500000000000 / 981481481481) ∧
    -Real.log (500000000000 / 981481481481) ≤ (84306881 / 125000000) := by
  have h := checkLog_sound (w := (481481481481 / 1481481481481)) (n := 12)
    (lo := (674455047 / 1000000000)) (hi := (84306881 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((981481481481 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(981481481481 / 500000000000) = 1/(500000000000 / 981481481481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10125 : Bounds (674455047 / 1000000000) (84306881 / 125000000) (Real.log (981481481481 / 500000000000)) := by
  have h := reflection_log_10125_neg
  have he : Real.log (981481481481 / 500000000000) = -Real.log (500000000000 / 981481481481) := by
    rw [show ((981481481481 / 500000000000) : ℝ) = ((500000000000 / 981481481481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10126_neg : (676692059 / 1000000000) ≤ -Real.log (500000000000 / 983679525223) ∧
    -Real.log (500000000000 / 983679525223) ≤ (33834603 / 50000000) := by
  have h := checkLog_sound (w := (483679525223 / 1483679525223)) (n := 12)
    (lo := (676692059 / 1000000000)) (hi := (33834603 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((983679525223 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(983679525223 / 500000000000) = 1/(500000000000 / 983679525223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10126 : Bounds (676692059 / 1000000000) (33834603 / 50000000) (Real.log (983679525223 / 500000000000)) := by
  have h := reflection_log_10126_neg
  have he : Real.log (983679525223 / 500000000000) = -Real.log (500000000000 / 983679525223) := by
    rw [show ((983679525223 / 500000000000) : ℝ) = ((500000000000 / 983679525223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10127_neg : (56584151 / 200000000) ≤ -Real.log (1000 / 1327) ∧
    -Real.log (1000 / 1327) ≤ (70730189 / 250000000) := by
  have h := checkLog_sound (w := (327 / 2327)) (n := 12)
    (lo := (56584151 / 200000000)) (hi := (70730189 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1327 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1327 / 1000) = 1/(1000 / 1327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10127 : Bounds (56584151 / 200000000) (70730189 / 250000000) (Real.log (1327 / 1000)) := by
  have h := reflection_log_10127_neg
  have he : Real.log (1327 / 1000) = -Real.log (1000 / 1327) := by
    rw [show ((1327 / 1000) : ℝ) = ((1000 / 1327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10128_neg : (396009949 / 1000000000) ≤ -Real.log (673 / 1000) ∧
    -Real.log (673 / 1000) ≤ (7920199 / 20000000) := by
  have h := checkLog_sound (w := (327 / 1673)) (n := 12)
    (lo := (396009949 / 1000000000)) (hi := (7920199 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 673) = 1/(673 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10128 : Bounds (-7920199 / 20000000) (-396009949 / 1000000000) (Real.log (673 / 1000)) := by
  have h := reflection_log_10128_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10129_neg : (163473 / 500000000) ≤ -Real.log (1000000 / 1000327) ∧
    -Real.log (1000000 / 1000327) ≤ (326947 / 1000000000) := by
  have h := checkLog_sound (w := (327 / 2000327)) (n := 12)
    (lo := (163473 / 500000000)) (hi := (326947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000327 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000327 / 1000000) = 1/(1000000 / 1000327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10129 : Bounds (163473 / 500000000) (326947 / 1000000000) (Real.log (1000327 / 1000000)) := by
  have h := reflection_log_10129_neg
  have he : Real.log (1000327 / 1000000) = -Real.log (1000000 / 1000327) := by
    rw [show ((1000327 / 1000000) : ℝ) = ((1000000 / 1000327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10130_neg : (327053 / 1000000000) ≤ -Real.log (999673 / 1000000) ∧
    -Real.log (999673 / 1000000) ≤ (163527 / 500000000) := by
  have h := checkLog_sound (w := (327 / 1999673)) (n := 12)
    (lo := (327053 / 1000000000)) (hi := (163527 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999673) = 1/(999673 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10130 : Bounds (-163527 / 500000000) (-327053 / 1000000000) (Real.log (999673 / 1000000)) := by
  have h := reflection_log_10130_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10131_neg : (9602177 / 62500000) ≤ -Real.log (200000 / 233213) ∧
    -Real.log (200000 / 233213) ≤ (153634833 / 1000000000) := by
  have h := checkLog_sound (w := (33213 / 433213)) (n := 12)
    (lo := (9602177 / 62500000)) (hi := (153634833 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233213 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233213 / 200000) = 1/(200000 / 233213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10131 : Bounds (9602177 / 62500000) (153634833 / 1000000000) (Real.log (233213 / 200000)) := by
  have h := reflection_log_10131_neg
  have he : Real.log (233213 / 200000) = -Real.log (200000 / 233213) := by
    rw [show ((233213 / 200000) : ℝ) = ((200000 / 233213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10132_neg : (181599817 / 1000000000) ≤ -Real.log (166787 / 200000) ∧
    -Real.log (166787 / 200000) ≤ (90799909 / 500000000) := by
  have h := checkLog_sound (w := (33213 / 366787)) (n := 12)
    (lo := (181599817 / 1000000000)) (hi := (90799909 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 166787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 166787) = 1/(166787 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10132 : Bounds (-90799909 / 500000000) (-181599817 / 1000000000) (Real.log (166787 / 200000)) := by
  have h := reflection_log_10132_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10133_neg : (38591307 / 250000000) ≤ -Real.log (1000000 / 1166917) ∧
    -Real.log (1000000 / 1166917) ≤ (154365229 / 1000000000) := by
  have h := checkLog_sound (w := (166917 / 2166917)) (n := 12)
    (lo := (38591307 / 250000000)) (hi := (154365229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1166917 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1166917 / 1000000) = 1/(1000000 / 1166917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10133 : Bounds (38591307 / 250000000) (154365229 / 1000000000) (Real.log (1166917 / 1000000)) := by
  have h := reflection_log_10133_neg
  have he : Real.log (1166917 / 1000000) = -Real.log (1000000 / 1166917) := by
    rw [show ((1166917 / 1000000) : ℝ) = ((1000000 / 1166917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10134_neg : (182622001 / 1000000000) ≤ -Real.log (833083 / 1000000) ∧
    -Real.log (833083 / 1000000) ≤ (91311001 / 500000000) := by
  have h := checkLog_sound (w := (166917 / 1833083)) (n := 12)
    (lo := (182622001 / 1000000000)) (hi := (91311001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 833083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 833083) = 1/(833083 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10134 : Bounds (-91311001 / 500000000) (-182622001 / 1000000000) (Real.log (833083 / 1000000)) := by
  have h := reflection_log_10134_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10135_neg : (28256773 / 1000000000) ≤ -Real.log (972138715111 / 1000000000000) ∧
    -Real.log (972138715111 / 1000000000000) ≤ (14128387 / 500000000) := by
  have h := checkLog_sound (w := (27861284889 / 1972138715111)) (n := 12)
    (lo := (28256773 / 1000000000)) (hi := (14128387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 972138715111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 972138715111) = 1/(972138715111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10135 : Bounds (-14128387 / 500000000) (-28256773 / 1000000000) (Real.log (972138715111 / 1000000000000)) := by
  have h := reflection_log_10135_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10136_neg : (3495623 / 125000000) ≤ -Real.log (38896896631 / 40000000000) ∧
    -Real.log (38896896631 / 40000000000) ≤ (5592997 / 200000000) := by
  have h := checkLog_sound (w := (1103103369 / 78896896631)) (n := 12)
    (lo := (3495623 / 125000000)) (hi := (5592997 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38896896631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38896896631) = 1/(38896896631 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10136 : Bounds (-5592997 / 200000000) (-3495623 / 125000000) (Real.log (38896896631 / 40000000000)) := by
  have h := reflection_log_10136_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10137_neg : (335234649 / 1000000000) ≤ -Real.log (500000000000 / 699134225089) ∧
    -Real.log (500000000000 / 699134225089) ≤ (6704693 / 20000000) := by
  have h := checkLog_sound (w := (199134225089 / 1199134225089)) (n := 12)
    (lo := (335234649 / 1000000000)) (hi := (6704693 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699134225089 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699134225089 / 500000000000) = 1/(500000000000 / 699134225089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10137 : Bounds (335234649 / 1000000000) (6704693 / 20000000) (Real.log (699134225089 / 500000000000)) := by
  have h := reflection_log_10137_neg
  have he : Real.log (699134225089 / 500000000000) = -Real.log (500000000000 / 699134225089) := by
    rw [show ((699134225089 / 500000000000) : ℝ) = ((500000000000 / 699134225089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10138_neg : (33698723 / 100000000) ≤ -Real.log (500000000000 / 700360588321) ∧
    -Real.log (500000000000 / 700360588321) ≤ (336987231 / 1000000000) := by
  have h := checkLog_sound (w := (200360588321 / 1200360588321)) (n := 12)
    (lo := (33698723 / 100000000)) (hi := (336987231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((700360588321 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(700360588321 / 500000000000) = 1/(500000000000 / 700360588321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10138 : Bounds (33698723 / 100000000) (336987231 / 1000000000) (Real.log (700360588321 / 500000000000)) := by
  have h := reflection_log_10138_neg
  have he : Real.log (700360588321 / 500000000000) = -Real.log (500000000000 / 700360588321) := by
    rw [show ((700360588321 / 500000000000) : ℝ) = ((500000000000 / 700360588321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10139_neg : (676692059 / 1000000000) ≤ -Real.log (250000000000 / 491839762611) ∧
    -Real.log (250000000000 / 491839762611) ≤ (33834603 / 50000000) := by
  have h := checkLog_sound (w := (241839762611 / 741839762611)) (n := 12)
    (lo := (676692059 / 1000000000)) (hi := (33834603 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491839762611 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491839762611 / 250000000000) = 1/(250000000000 / 491839762611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10139 : Bounds (676692059 / 1000000000) (33834603 / 50000000) (Real.log (491839762611 / 250000000000)) := by
  have h := reflection_log_10139_neg
  have he : Real.log (491839762611 / 250000000000) = -Real.log (250000000000 / 491839762611) := by
    rw [show ((491839762611 / 250000000000) : ℝ) = ((250000000000 / 491839762611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10140_neg : (42433169 / 62500000) ≤ -Real.log (500000000000 / 985884101041) ∧
    -Real.log (500000000000 / 985884101041) ≤ (135786141 / 200000000) := by
  have h := checkLog_sound (w := (485884101041 / 1485884101041)) (n := 12)
    (lo := (42433169 / 62500000)) (hi := (135786141 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((985884101041 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(985884101041 / 500000000000) = 1/(500000000000 / 985884101041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10140 : Bounds (42433169 / 62500000) (135786141 / 200000000) (Real.log (985884101041 / 500000000000)) := by
  have h := reflection_log_10140_neg
  have he : Real.log (985884101041 / 500000000000) = -Real.log (500000000000 / 985884101041) := by
    rw [show ((985884101041 / 500000000000) : ℝ) = ((500000000000 / 985884101041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10141_neg : (283674051 / 1000000000) ≤ -Real.log (125 / 166) ∧
    -Real.log (125 / 166) ≤ (70918513 / 250000000) := by
  have h := checkLog_sound (w := (41 / 291)) (n := 12)
    (lo := (283674051 / 1000000000)) (hi := (70918513 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(166 / 125) = 1/(125 / 166) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10141 : Bounds (283674051 / 1000000000) (70918513 / 250000000) (Real.log (166 / 125)) := by
  have h := reflection_log_10141_neg
  have he : Real.log (166 / 125) = -Real.log (125 / 166) := by
    rw [show ((166 / 125) : ℝ) = ((125 / 166) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10142_neg : (198748469 / 500000000) ≤ -Real.log (84 / 125) ∧
    -Real.log (84 / 125) ≤ (397496939 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 209)) (n := 12)
    (lo := (198748469 / 500000000)) (hi := (397496939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 84) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 84) = 1/(84 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10142 : Bounds (-397496939 / 1000000000) (-198748469 / 500000000) (Real.log (84 / 125)) := by
  have h := reflection_log_10142_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10143_neg : (163973 / 500000000) ≤ -Real.log (125000 / 125041) ∧
    -Real.log (125000 / 125041) ≤ (327947 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 250041)) (n := 12)
    (lo := (163973 / 500000000)) (hi := (327947 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125041 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125041 / 125000) = 1/(125000 / 125041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10143 : Bounds (163973 / 500000000) (327947 / 1000000000) (Real.log (125041 / 125000)) := by
  have h := reflection_log_10143_neg
  have he : Real.log (125041 / 125000) = -Real.log (125000 / 125041) := by
    rw [show ((125041 / 125000) : ℝ) = ((125000 / 125041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10144_neg : (328053 / 1000000000) ≤ -Real.log (124959 / 125000) ∧
    -Real.log (124959 / 125000) ≤ (164027 / 500000000) := by
  have h := checkLog_sound (w := (41 / 249959)) (n := 12)
    (lo := (328053 / 1000000000)) (hi := (164027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124959) = 1/(124959 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10144 : Bounds (-164027 / 500000000) (-328053 / 1000000000) (Real.log (124959 / 125000)) := by
  have h := reflection_log_10144_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10145_neg : (154089249 / 1000000000) ≤ -Real.log (200000 / 233319) ∧
    -Real.log (200000 / 233319) ≤ (616357 / 4000000) := by
  have h := checkLog_sound (w := (33319 / 433319)) (n := 12)
    (lo := (154089249 / 1000000000)) (hi := (616357 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233319 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233319 / 200000) = 1/(200000 / 233319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10145 : Bounds (154089249 / 1000000000) (616357 / 4000000) (Real.log (233319 / 200000)) := by
  have h := reflection_log_10145_neg
  have he : Real.log (233319 / 200000) = -Real.log (200000 / 233319) := by
    rw [show ((233319 / 200000) : ℝ) = ((200000 / 233319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10146_neg : (4555889 / 25000000) ≤ -Real.log (166681 / 200000) ∧
    -Real.log (166681 / 200000) ≤ (182235561 / 1000000000) := by
  have h := checkLog_sound (w := (33319 / 366681)) (n := 12)
    (lo := (4555889 / 25000000)) (hi := (182235561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 166681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 166681) = 1/(166681 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10146 : Bounds (-182235561 / 1000000000) (-4555889 / 25000000) (Real.log (166681 / 200000)) := by
  have h := reflection_log_10146_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10147_neg : (154820169 / 1000000000) ≤ -Real.log (125000 / 145931) ∧
    -Real.log (125000 / 145931) ≤ (15482017 / 100000000) := by
  have h := checkLog_sound (w := (20931 / 270931)) (n := 12)
    (lo := (154820169 / 1000000000)) (hi := (15482017 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145931 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145931 / 125000) = 1/(125000 / 145931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10147 : Bounds (154820169 / 1000000000) (15482017 / 100000000) (Real.log (145931 / 125000)) := by
  have h := reflection_log_10147_neg
  have he : Real.log (145931 / 125000) = -Real.log (125000 / 145931) := by
    rw [show ((145931 / 125000) : ℝ) = ((125000 / 145931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10148_neg : (45814899 / 250000000) ≤ -Real.log (104069 / 125000) ∧
    -Real.log (104069 / 125000) ≤ (183259597 / 1000000000) := by
  have h := checkLog_sound (w := (20931 / 229069)) (n := 12)
    (lo := (45814899 / 250000000)) (hi := (183259597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 104069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 104069) = 1/(104069 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10148 : Bounds (-183259597 / 1000000000) (-45814899 / 250000000) (Real.log (104069 / 125000)) := by
  have h := reflection_log_10148_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10149_neg : (14219713 / 500000000) ≤ -Real.log (15186893239 / 15625000000) ∧
    -Real.log (15186893239 / 15625000000) ≤ (28439427 / 1000000000) := by
  have h := checkLog_sound (w := (438106761 / 30811893239)) (n := 12)
    (lo := (14219713 / 500000000)) (hi := (28439427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15186893239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15186893239) = 1/(15186893239 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10149 : Bounds (-28439427 / 1000000000) (-14219713 / 500000000) (Real.log (15186893239 / 15625000000)) := by
  have h := reflection_log_10149_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10150_neg : (28146311 / 1000000000) ≤ -Real.log (38889844239 / 40000000000) ∧
    -Real.log (38889844239 / 40000000000) ≤ (3518289 / 125000000) := by
  have h := checkLog_sound (w := (1110155761 / 78889844239)) (n := 12)
    (lo := (28146311 / 1000000000)) (hi := (3518289 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38889844239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38889844239) = 1/(38889844239 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10150 : Bounds (-3518289 / 125000000) (-28146311 / 1000000000) (Real.log (38889844239 / 40000000000)) := by
  have h := reflection_log_10150_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10151_neg : (336324809 / 1000000000) ≤ -Real.log (250000000000 / 349948404437) ∧
    -Real.log (250000000000 / 349948404437) ≤ (33632481 / 100000000) := by
  have h := checkLog_sound (w := (99948404437 / 599948404437)) (n := 12)
    (lo := (336324809 / 1000000000)) (hi := (33632481 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349948404437 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(349948404437 / 250000000000) = 1/(250000000000 / 349948404437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10151 : Bounds (336324809 / 1000000000) (33632481 / 100000000) (Real.log (349948404437 / 250000000000)) := by
  have h := reflection_log_10151_neg
  have he : Real.log (349948404437 / 250000000000) = -Real.log (250000000000 / 349948404437) := by
    rw [show ((349948404437 / 250000000000) : ℝ) = ((250000000000 / 349948404437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10152_neg : (169039883 / 500000000) ≤ -Real.log (500000000000 / 701126175903) ∧
    -Real.log (500000000000 / 701126175903) ≤ (338079767 / 1000000000) := by
  have h := checkLog_sound (w := (201126175903 / 1201126175903)) (n := 12)
    (lo := (169039883 / 500000000)) (hi := (338079767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((701126175903 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(701126175903 / 500000000000) = 1/(500000000000 / 701126175903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10152 : Bounds (169039883 / 500000000) (338079767 / 1000000000) (Real.log (701126175903 / 500000000000)) := by
  have h := reflection_log_10152_neg
  have he : Real.log (701126175903 / 500000000000) = -Real.log (500000000000 / 701126175903) := by
    rw [show ((701126175903 / 500000000000) : ℝ) = ((500000000000 / 701126175903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10153_neg : (42433169 / 62500000) ≤ -Real.log (6250000000 / 12323551263) ∧
    -Real.log (6250000000 / 12323551263) ≤ (135786141 / 200000000) := by
  have h := checkLog_sound (w := (6073551263 / 18573551263)) (n := 12)
    (lo := (42433169 / 62500000)) (hi := (135786141 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12323551263 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12323551263 / 6250000000) = 1/(6250000000 / 12323551263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10153 : Bounds (42433169 / 62500000) (135786141 / 200000000) (Real.log (12323551263 / 6250000000)) := by
  have h := reflection_log_10153_neg
  have he : Real.log (12323551263 / 6250000000) = -Real.log (6250000000 / 12323551263) := by
    rw [show ((12323551263 / 6250000000) : ℝ) = ((6250000000 / 12323551263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10154_neg : (681170989 / 1000000000) ≤ -Real.log (31250000000 / 61755952381) ∧
    -Real.log (31250000000 / 61755952381) ≤ (68117099 / 100000000) := by
  have h := checkLog_sound (w := (30505952381 / 93005952381)) (n := 12)
    (lo := (681170989 / 1000000000)) (hi := (68117099 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61755952381 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61755952381 / 31250000000) = 1/(31250000000 / 61755952381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10154 : Bounds (681170989 / 1000000000) (68117099 / 100000000) (Real.log (61755952381 / 31250000000)) := by
  have h := reflection_log_10154_neg
  have he : Real.log (61755952381 / 31250000000) = -Real.log (31250000000 / 61755952381) := by
    rw [show ((61755952381 / 31250000000) : ℝ) = ((31250000000 / 61755952381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10155_neg : (284426779 / 1000000000) ≤ -Real.log (1000 / 1329) ∧
    -Real.log (1000 / 1329) ≤ (14221339 / 50000000) := by
  have h := checkLog_sound (w := (329 / 2329)) (n := 12)
    (lo := (284426779 / 1000000000)) (hi := (14221339 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1329 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1329 / 1000) = 1/(1000 / 1329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10155 : Bounds (284426779 / 1000000000) (14221339 / 50000000) (Real.log (1329 / 1000)) := by
  have h := reflection_log_10155_neg
  have he : Real.log (1329 / 1000) = -Real.log (1000 / 1329) := by
    rw [show ((1329 / 1000) : ℝ) = ((1000 / 1329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10156_neg : (199493071 / 500000000) ≤ -Real.log (671 / 1000) ∧
    -Real.log (671 / 1000) ≤ (398986143 / 1000000000) := by
  have h := checkLog_sound (w := (329 / 1671)) (n := 12)
    (lo := (199493071 / 500000000)) (hi := (398986143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 671) = 1/(671 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10156 : Bounds (-398986143 / 1000000000) (-199493071 / 500000000) (Real.log (671 / 1000)) := by
  have h := reflection_log_10156_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10157_neg : (65789 / 200000000) ≤ -Real.log (1000000 / 1000329) ∧
    -Real.log (1000000 / 1000329) ≤ (164473 / 500000000) := by
  have h := checkLog_sound (w := (329 / 2000329)) (n := 12)
    (lo := (65789 / 200000000)) (hi := (164473 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000329 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000329 / 1000000) = 1/(1000000 / 1000329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10157 : Bounds (65789 / 200000000) (164473 / 500000000) (Real.log (1000329 / 1000000)) := by
  have h := reflection_log_10157_neg
  have he : Real.log (1000329 / 1000000) = -Real.log (1000000 / 1000329) := by
    rw [show ((1000329 / 1000000) : ℝ) = ((1000000 / 1000329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10158_neg : (164527 / 500000000) ≤ -Real.log (999671 / 1000000) ∧
    -Real.log (999671 / 1000000) ≤ (65811 / 200000000) := by
  have h := checkLog_sound (w := (329 / 1999671)) (n := 12)
    (lo := (164527 / 500000000)) (hi := (65811 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999671) = 1/(999671 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10158 : Bounds (-65811 / 200000000) (-164527 / 500000000) (Real.log (999671 / 1000000)) := by
  have h := reflection_log_10158_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10159_neg : (38636079 / 250000000) ≤ -Real.log (500000 / 583563) ∧
    -Real.log (500000 / 583563) ≤ (154544317 / 1000000000) := by
  have h := checkLog_sound (w := (83563 / 1083563)) (n := 12)
    (lo := (38636079 / 250000000)) (hi := (154544317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583563 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583563 / 500000) = 1/(500000 / 583563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10159 : Bounds (38636079 / 250000000) (154544317 / 1000000000) (Real.log (583563 / 500000)) := by
  have h := reflection_log_10159_neg
  have he : Real.log (583563 / 500000) = -Real.log (500000 / 583563) := by
    rw [show ((583563 / 500000) : ℝ) = ((500000 / 583563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10160_neg : (45718227 / 250000000) ≤ -Real.log (416437 / 500000) ∧
    -Real.log (416437 / 500000) ≤ (182872909 / 1000000000) := by
  have h := checkLog_sound (w := (83563 / 916437)) (n := 12)
    (lo := (45718227 / 250000000)) (hi := (182872909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 416437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 416437) = 1/(416437 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10160 : Bounds (-182872909 / 1000000000) (-45718227 / 250000000) (Real.log (416437 / 500000)) := by
  have h := reflection_log_10160_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10161_neg : (19409363 / 125000000) ≤ -Real.log (1000000 / 1167979) ∧
    -Real.log (1000000 / 1167979) ≤ (31054981 / 200000000) := by
  have h := checkLog_sound (w := (167979 / 2167979)) (n := 12)
    (lo := (19409363 / 125000000)) (hi := (31054981 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1167979 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1167979 / 1000000) = 1/(1000000 / 1167979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10161 : Bounds (19409363 / 125000000) (31054981 / 200000000) (Real.log (1167979 / 1000000)) := by
  have h := reflection_log_10161_neg
  have he : Real.log (1167979 / 1000000) = -Real.log (1000000 / 1167979) := by
    rw [show ((1167979 / 1000000) : ℝ) = ((1000000 / 1167979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10162_neg : (91948799 / 500000000) ≤ -Real.log (832021 / 1000000) ∧
    -Real.log (832021 / 1000000) ≤ (183897599 / 1000000000) := by
  have h := checkLog_sound (w := (167979 / 1832021)) (n := 12)
    (lo := (91948799 / 500000000)) (hi := (183897599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 832021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 832021) = 1/(832021 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10162 : Bounds (-183897599 / 1000000000) (-91948799 / 500000000) (Real.log (832021 / 1000000)) := by
  have h := reflection_log_10162_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10163_neg : (28622693 / 1000000000) ≤ -Real.log (971783055559 / 1000000000000) ∧
    -Real.log (971783055559 / 1000000000000) ≤ (14311347 / 500000000) := by
  have h := checkLog_sound (w := (28216944441 / 1971783055559)) (n := 12)
    (lo := (28622693 / 1000000000)) (hi := (14311347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 971783055559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 971783055559) = 1/(971783055559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10163 : Bounds (-14311347 / 500000000) (-28622693 / 1000000000) (Real.log (971783055559 / 1000000000000)) := by
  have h := reflection_log_10163_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10164_neg : (1770537 / 62500000) ≤ -Real.log (243017225031 / 250000000000) ∧
    -Real.log (243017225031 / 250000000000) ≤ (28328593 / 1000000000) := by
  have h := checkLog_sound (w := (6982774969 / 493017225031)) (n := 12)
    (lo := (1770537 / 62500000)) (hi := (28328593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 243017225031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 243017225031) = 1/(243017225031 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10164 : Bounds (-28328593 / 1000000000) (-1770537 / 62500000) (Real.log (243017225031 / 250000000000)) := by
  have h := reflection_log_10164_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10165_neg : (13496689 / 40000000) ≤ -Real.log (250000000000 / 350330902393) ∧
    -Real.log (250000000000 / 350330902393) ≤ (168708613 / 500000000) := by
  have h := checkLog_sound (w := (100330902393 / 600330902393)) (n := 12)
    (lo := (13496689 / 40000000)) (hi := (168708613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((350330902393 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(350330902393 / 250000000000) = 1/(250000000000 / 350330902393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10165 : Bounds (13496689 / 40000000) (168708613 / 500000000) (Real.log (350330902393 / 250000000000)) := by
  have h := reflection_log_10165_neg
  have he : Real.log (350330902393 / 250000000000) = -Real.log (250000000000 / 350330902393) := by
    rw [show ((350330902393 / 250000000000) : ℝ) = ((250000000000 / 350330902393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10166_neg : (169586251 / 500000000) ≤ -Real.log (500000000000 / 701892740689) ∧
    -Real.log (500000000000 / 701892740689) ≤ (339172503 / 1000000000) := by
  have h := checkLog_sound (w := (201892740689 / 1201892740689)) (n := 12)
    (lo := (169586251 / 500000000)) (hi := (339172503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((701892740689 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(701892740689 / 500000000000) = 1/(500000000000 / 701892740689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10166 : Bounds (169586251 / 500000000) (339172503 / 1000000000) (Real.log (701892740689 / 500000000000)) := by
  have h := reflection_log_10166_neg
  have he : Real.log (701892740689 / 500000000000) = -Real.log (500000000000 / 701892740689) := by
    rw [show ((701892740689 / 500000000000) : ℝ) = ((500000000000 / 701892740689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10167_neg : (681170989 / 1000000000) ≤ -Real.log (100000000000 / 197619047619) ∧
    -Real.log (100000000000 / 197619047619) ≤ (68117099 / 100000000) := by
  have h := checkLog_sound (w := (97619047619 / 297619047619)) (n := 12)
    (lo := (681170989 / 1000000000)) (hi := (68117099 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((197619047619 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(197619047619 / 100000000000) = 1/(100000000000 / 197619047619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10167 : Bounds (681170989 / 1000000000) (68117099 / 100000000) (Real.log (197619047619 / 100000000000)) := by
  have h := reflection_log_10167_neg
  have he : Real.log (197619047619 / 100000000000) = -Real.log (100000000000 / 197619047619) := by
    rw [show ((197619047619 / 100000000000) : ℝ) = ((100000000000 / 197619047619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10168_neg : (683412921 / 1000000000) ≤ -Real.log (500000000000 / 990312965723) ∧
    -Real.log (500000000000 / 990312965723) ≤ (341706461 / 500000000) := by
  have h := checkLog_sound (w := (490312965723 / 1490312965723)) (n := 12)
    (lo := (683412921 / 1000000000)) (hi := (341706461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((990312965723 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(990312965723 / 500000000000) = 1/(500000000000 / 990312965723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10168 : Bounds (683412921 / 1000000000) (341706461 / 500000000) (Real.log (990312965723 / 500000000000)) := by
  have h := reflection_log_10168_neg
  have he : Real.log (990312965723 / 500000000000) = -Real.log (500000000000 / 990312965723) := by
    rw [show ((990312965723 / 500000000000) : ℝ) = ((500000000000 / 990312965723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10169_neg : (142589471 / 500000000) ≤ -Real.log (100 / 133) ∧
    -Real.log (100 / 133) ≤ (285178943 / 1000000000) := by
  have h := checkLog_sound (w := (33 / 233)) (n := 12)
    (lo := (142589471 / 500000000)) (hi := (285178943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((133 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(133 / 100) = 1/(100 / 133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10169 : Bounds (142589471 / 500000000) (285178943 / 1000000000) (Real.log (133 / 100)) := by
  have h := reflection_log_10169_neg
  have he : Real.log (133 / 100) = -Real.log (100 / 133) := by
    rw [show ((133 / 100) : ℝ) = ((100 / 133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10170_neg : (200238783 / 500000000) ≤ -Real.log (67 / 100) ∧
    -Real.log (67 / 100) ≤ (400477567 / 1000000000) := by
  have h := checkLog_sound (w := (33 / 167)) (n := 12)
    (lo := (200238783 / 500000000)) (hi := (400477567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 67) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 67) = 1/(67 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10170 : Bounds (-400477567 / 1000000000) (-200238783 / 500000000) (Real.log (67 / 100)) := by
  have h := reflection_log_10170_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10171_neg : (65989 / 200000000) ≤ -Real.log (100000 / 100033) ∧
    -Real.log (100000 / 100033) ≤ (164973 / 500000000) := by
  have h := checkLog_sound (w := (33 / 200033)) (n := 12)
    (lo := (65989 / 200000000)) (hi := (164973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100033 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100033 / 100000) = 1/(100000 / 100033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10171 : Bounds (65989 / 200000000) (164973 / 500000000) (Real.log (100033 / 100000)) := by
  have h := reflection_log_10171_neg
  have he : Real.log (100033 / 100000) = -Real.log (100000 / 100033) := by
    rw [show ((100033 / 100000) : ℝ) = ((100000 / 100033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10172_neg : (165027 / 500000000) ≤ -Real.log (99967 / 100000) ∧
    -Real.log (99967 / 100000) ≤ (66011 / 200000000) := by
  have h := checkLog_sound (w := (33 / 199967)) (n := 12)
    (lo := (165027 / 500000000)) (hi := (66011 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99967) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99967) = 1/(99967 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10172 : Bounds (-66011 / 200000000) (-165027 / 500000000) (Real.log (99967 / 100000)) := by
  have h := reflection_log_10172_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10173_neg : (1937479 / 12500000) ≤ -Real.log (125000 / 145957) ∧
    -Real.log (125000 / 145957) ≤ (154998321 / 1000000000) := by
  have h := checkLog_sound (w := (20957 / 270957)) (n := 12)
    (lo := (1937479 / 12500000)) (hi := (154998321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((145957 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(145957 / 125000) = 1/(125000 / 145957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10173 : Bounds (1937479 / 12500000) (154998321 / 1000000000) (Real.log (145957 / 125000)) := by
  have h := reflection_log_10173_neg
  have he : Real.log (145957 / 125000) = -Real.log (125000 / 145957) := by
    rw [show ((145957 / 125000) : ℝ) = ((125000 / 145957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10174_neg : (91754731 / 500000000) ≤ -Real.log (104043 / 125000) ∧
    -Real.log (104043 / 125000) ≤ (183509463 / 1000000000) := by
  have h := checkLog_sound (w := (20957 / 229043)) (n := 12)
    (lo := (91754731 / 500000000)) (hi := (183509463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 104043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 104043) = 1/(104043 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10174 : Bounds (-183509463 / 1000000000) (-91754731 / 500000000) (Real.log (104043 / 125000)) := by
  have h := reflection_log_10174_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10175_neg : (9733143 / 62500000) ≤ -Real.log (1000000 / 1168511) ∧
    -Real.log (1000000 / 1168511) ≤ (155730289 / 1000000000) := by
  have h := checkLog_sound (w := (168511 / 2168511)) (n := 12)
    (lo := (9733143 / 62500000)) (hi := (155730289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1168511 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1168511 / 1000000) = 1/(1000000 / 1168511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10175 : Bounds (9733143 / 62500000) (155730289 / 1000000000) (Real.log (1168511 / 1000000)) := by
  have h := reflection_log_10175_neg
  have he : Real.log (1168511 / 1000000) = -Real.log (1000000 / 1168511) := by
    rw [show ((1168511 / 1000000) : ℝ) = ((1000000 / 1168511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
