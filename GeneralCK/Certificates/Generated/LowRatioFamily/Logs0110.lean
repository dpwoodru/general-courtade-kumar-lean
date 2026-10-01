import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7040_neg : (1134503 / 5000000) ≤ -Real.log (797 / 1000) ∧
    -Real.log (797 / 1000) ≤ (226900601 / 1000000000) := by
  have h := checkLog_sound (w := (203 / 1797)) (n := 12)
    (lo := (1134503 / 5000000)) (hi := (226900601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 797) = 1/(797 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7040 : Bounds (-226900601 / 1000000000) (-1134503 / 5000000) (Real.log (797 / 1000)) := by
  have h := reflection_log_7040_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7041_neg : (202979 / 1000000000) ≤ -Real.log (1000000 / 1000203) ∧
    -Real.log (1000000 / 1000203) ≤ (10149 / 50000000) := by
  have h := checkLog_sound (w := (203 / 2000203)) (n := 12)
    (lo := (202979 / 1000000000)) (hi := (10149 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000203 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000203 / 1000000) = 1/(1000000 / 1000203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7041 : Bounds (202979 / 1000000000) (10149 / 50000000) (Real.log (1000203 / 1000000)) := by
  have h := reflection_log_7041_neg
  have he : Real.log (1000203 / 1000000) = -Real.log (1000000 / 1000203) := by
    rw [show ((1000203 / 1000000) : ℝ) = ((1000000 / 1000203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7042_neg : (10151 / 50000000) ≤ -Real.log (999797 / 1000000) ∧
    -Real.log (999797 / 1000000) ≤ (203021 / 1000000000) := by
  have h := checkLog_sound (w := (203 / 1999797)) (n := 12)
    (lo := (10151 / 50000000)) (hi := (203021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999797) = 1/(999797 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7042 : Bounds (-203021 / 1000000000) (-10151 / 50000000) (Real.log (999797 / 1000000)) := by
  have h := reflection_log_7042_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7043_neg : (19408463 / 200000000) ≤ -Real.log (1000000 / 1101907) ∧
    -Real.log (1000000 / 1101907) ≤ (24260579 / 250000000) := by
  have h := checkLog_sound (w := (101907 / 2101907)) (n := 12)
    (lo := (19408463 / 200000000)) (hi := (24260579 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1101907 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1101907 / 1000000) = 1/(1000000 / 1101907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7043 : Bounds (19408463 / 200000000) (24260579 / 250000000) (Real.log (1101907 / 1000000)) := by
  have h := reflection_log_7043_neg
  have he : Real.log (1101907 / 1000000) = -Real.log (1000000 / 1101907) := by
    rw [show ((1101907 / 1000000) : ℝ) = ((1000000 / 1101907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7044_neg : (26870413 / 250000000) ≤ -Real.log (898093 / 1000000) ∧
    -Real.log (898093 / 1000000) ≤ (107481653 / 1000000000) := by
  have h := checkLog_sound (w := (101907 / 1898093)) (n := 12)
    (lo := (26870413 / 250000000)) (hi := (107481653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 898093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 898093) = 1/(898093 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7044 : Bounds (-107481653 / 1000000000) (-26870413 / 250000000) (Real.log (898093 / 1000000)) := by
  have h := reflection_log_7044_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7045_neg : (97457871 / 1000000000) ≤ -Real.log (200000 / 220473) ∧
    -Real.log (200000 / 220473) ≤ (6091117 / 62500000) := by
  have h := checkLog_sound (w := (20473 / 420473)) (n := 12)
    (lo := (97457871 / 1000000000)) (hi := (6091117 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((220473 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(220473 / 200000) = 1/(200000 / 220473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7045 : Bounds (97457871 / 1000000000) (6091117 / 62500000) (Real.log (220473 / 200000)) := by
  have h := reflection_log_7045_neg
  have he : Real.log (220473 / 200000) = -Real.log (200000 / 220473) := by
    rw [show ((220473 / 200000) : ℝ) = ((200000 / 220473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7046_neg : (13498969 / 125000000) ≤ -Real.log (179527 / 200000) ∧
    -Real.log (179527 / 200000) ≤ (107991753 / 1000000000) := by
  have h := checkLog_sound (w := (20473 / 379527)) (n := 12)
    (lo := (13498969 / 125000000)) (hi := (107991753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 179527) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 179527) = 1/(179527 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7046 : Bounds (-107991753 / 1000000000) (-13498969 / 125000000) (Real.log (179527 / 200000)) := by
  have h := reflection_log_7046_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7047_neg : (263347 / 25000000) ≤ -Real.log (39580856271 / 40000000000) ∧
    -Real.log (39580856271 / 40000000000) ≤ (10533881 / 1000000000) := by
  have h := checkLog_sound (w := (419143729 / 79580856271)) (n := 12)
    (lo := (263347 / 25000000)) (hi := (10533881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39580856271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39580856271) = 1/(39580856271 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7047 : Bounds (-10533881 / 1000000000) (-263347 / 25000000) (Real.log (39580856271 / 40000000000)) := by
  have h := reflection_log_7047_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7048_neg : (10439337 / 1000000000) ≤ -Real.log (989614963351 / 1000000000000) ∧
    -Real.log (989614963351 / 1000000000000) ≤ (5219669 / 500000000) := by
  have h := checkLog_sound (w := (10385036649 / 1989614963351)) (n := 12)
    (lo := (10439337 / 1000000000)) (hi := (5219669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989614963351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989614963351) = 1/(989614963351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7048 : Bounds (-5219669 / 500000000) (-10439337 / 1000000000) (Real.log (989614963351 / 1000000000000)) := by
  have h := reflection_log_7048_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7049_neg : (204523967 / 1000000000) ≤ -Real.log (100000000000 / 122694086247) ∧
    -Real.log (100000000000 / 122694086247) ≤ (3195687 / 15625000) := by
  have h := checkLog_sound (w := (22694086247 / 222694086247)) (n := 12)
    (lo := (204523967 / 1000000000)) (hi := (3195687 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122694086247 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122694086247 / 100000000000) = 1/(100000000000 / 122694086247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7049 : Bounds (204523967 / 1000000000) (3195687 / 15625000) (Real.log (122694086247 / 100000000000)) := by
  have h := reflection_log_7049_neg
  have he : Real.log (122694086247 / 100000000000) = -Real.log (100000000000 / 122694086247) := by
    rw [show ((122694086247 / 100000000000) : ℝ) = ((100000000000 / 122694086247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7050_neg : (205449623 / 1000000000) ≤ -Real.log (800000000 / 982461691) ∧
    -Real.log (800000000 / 982461691) ≤ (25681203 / 125000000) := by
  have h := checkLog_sound (w := (182461691 / 1782461691)) (n := 12)
    (lo := (205449623 / 1000000000)) (hi := (25681203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((982461691 / 800000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(982461691 / 800000000) = 1/(800000000 / 982461691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7050 : Bounds (205449623 / 1000000000) (25681203 / 125000000) (Real.log (982461691 / 800000000)) := by
  have h := reflection_log_7050_neg
  have he : Real.log (982461691 / 800000000) = -Real.log (800000000 / 982461691) := by
    rw [show ((982461691 / 800000000) : ℝ) = ((800000000 / 982461691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7051_neg : (410676167 / 1000000000) ≤ -Real.log (500000000000 / 753918495297) ∧
    -Real.log (500000000000 / 753918495297) ≤ (51334521 / 125000000) := by
  have h := checkLog_sound (w := (253918495297 / 1253918495297)) (n := 12)
    (lo := (410676167 / 1000000000)) (hi := (51334521 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((753918495297 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(753918495297 / 500000000000) = 1/(500000000000 / 753918495297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7051 : Bounds (410676167 / 1000000000) (51334521 / 125000000) (Real.log (753918495297 / 500000000000)) := by
  have h := reflection_log_7051_neg
  have he : Real.log (753918495297 / 500000000000) = -Real.log (500000000000 / 753918495297) := by
    rw [show ((753918495297 / 500000000000) : ℝ) = ((500000000000 / 753918495297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7052_neg : (411719037 / 1000000000) ≤ -Real.log (125000000000 / 188676286073) ∧
    -Real.log (125000000000 / 188676286073) ≤ (205859519 / 500000000) := by
  have h := checkLog_sound (w := (63676286073 / 313676286073)) (n := 12)
    (lo := (411719037 / 1000000000)) (hi := (205859519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((188676286073 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(188676286073 / 125000000000) = 1/(125000000000 / 188676286073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7052 : Bounds (411719037 / 1000000000) (205859519 / 500000000) (Real.log (188676286073 / 125000000000)) := by
  have h := reflection_log_7052_neg
  have he : Real.log (188676286073 / 125000000000) = -Real.log (125000000000 / 188676286073) := by
    rw [show ((188676286073 / 125000000000) : ℝ) = ((125000000000 / 188676286073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7053_neg : (92616989 / 500000000) ≤ -Real.log (2000 / 2407) ∧
    -Real.log (2000 / 2407) ≤ (185233979 / 1000000000) := by
  have h := checkLog_sound (w := (407 / 4407)) (n := 12)
    (lo := (92616989 / 500000000)) (hi := (185233979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2407 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2407 / 2000) = 1/(2000 / 2407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7053 : Bounds (92616989 / 500000000) (185233979 / 1000000000) (Real.log (2407 / 2000)) := by
  have h := reflection_log_7053_neg
  have he : Real.log (2407 / 2000) = -Real.log (2000 / 2407) := by
    rw [show ((2407 / 2000) : ℝ) = ((2000 / 2407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7054_neg : (227528149 / 1000000000) ≤ -Real.log (1593 / 2000) ∧
    -Real.log (1593 / 2000) ≤ (4550563 / 20000000) := by
  have h := checkLog_sound (w := (407 / 3593)) (n := 12)
    (lo := (227528149 / 1000000000)) (hi := (4550563 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1593) = 1/(1593 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7054 : Bounds (-4550563 / 20000000) (-227528149 / 1000000000) (Real.log (1593 / 2000)) := by
  have h := reflection_log_7054_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7055_neg : (203479 / 1000000000) ≤ -Real.log (2000000 / 2000407) ∧
    -Real.log (2000000 / 2000407) ≤ (5087 / 25000000) := by
  have h := checkLog_sound (w := (407 / 4000407)) (n := 12)
    (lo := (203479 / 1000000000)) (hi := (5087 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000407 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000407 / 2000000) = 1/(2000000 / 2000407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7055 : Bounds (203479 / 1000000000) (5087 / 25000000) (Real.log (2000407 / 2000000)) := by
  have h := reflection_log_7055_neg
  have he : Real.log (2000407 / 2000000) = -Real.log (2000000 / 2000407) := by
    rw [show ((2000407 / 2000000) : ℝ) = ((2000000 / 2000407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7056_neg : (159 / 781250) ≤ -Real.log (1999593 / 2000000) ∧
    -Real.log (1999593 / 2000000) ≤ (203521 / 1000000000) := by
  have h := checkLog_sound (w := (407 / 3999593)) (n := 12)
    (lo := (159 / 781250)) (hi := (203521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999593) = 1/(1999593 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7056 : Bounds (-203521 / 1000000000) (-159 / 781250) (Real.log (1999593 / 2000000)) := by
  have h := reflection_log_7056_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7057_neg : (19454741 / 200000000) ≤ -Real.log (500000 / 551081) ∧
    -Real.log (500000 / 551081) ≤ (48636853 / 500000000) := by
  have h := checkLog_sound (w := (51081 / 1051081)) (n := 12)
    (lo := (19454741 / 200000000)) (hi := (48636853 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((551081 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(551081 / 500000) = 1/(500000 / 551081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7057 : Bounds (19454741 / 200000000) (48636853 / 500000000) (Real.log (551081 / 500000)) := by
  have h := reflection_log_7057_neg
  have he : Real.log (551081 / 500000) = -Real.log (500000 / 551081) := by
    rw [show ((551081 / 500000) : ℝ) = ((500000 / 551081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7058_neg : (107765627 / 1000000000) ≤ -Real.log (448919 / 500000) ∧
    -Real.log (448919 / 500000) ≤ (26941407 / 250000000) := by
  have h := checkLog_sound (w := (51081 / 948919)) (n := 12)
    (lo := (107765627 / 1000000000)) (hi := (26941407 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 448919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 448919) = 1/(448919 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7058 : Bounds (-26941407 / 250000000) (-107765627 / 1000000000) (Real.log (448919 / 500000)) := by
  have h := reflection_log_7058_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7059_neg : (12211259 / 125000000) ≤ -Real.log (1000000 / 1102621) ∧
    -Real.log (1000000 / 1102621) ≤ (97690073 / 1000000000) := by
  have h := checkLog_sound (w := (102621 / 2102621)) (n := 12)
    (lo := (12211259 / 125000000)) (hi := (97690073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1102621 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1102621 / 1000000) = 1/(1000000 / 1102621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7059 : Bounds (12211259 / 125000000) (97690073 / 1000000000) (Real.log (1102621 / 1000000)) := by
  have h := reflection_log_7059_neg
  have he : Real.log (1102621 / 1000000) = -Real.log (1000000 / 1102621) := by
    rw [show ((1102621 / 1000000) : ℝ) = ((1000000 / 1102621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7060_neg : (54138493 / 500000000) ≤ -Real.log (897379 / 1000000) ∧
    -Real.log (897379 / 1000000) ≤ (108276987 / 1000000000) := by
  have h := checkLog_sound (w := (102621 / 1897379)) (n := 12)
    (lo := (54138493 / 500000000)) (hi := (108276987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 897379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 897379) = 1/(897379 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7060 : Bounds (-108276987 / 1000000000) (-54138493 / 500000000) (Real.log (897379 / 1000000)) := by
  have h := reflection_log_7060_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7061_neg : (10586913 / 1000000000) ≤ -Real.log (989468930359 / 1000000000000) ∧
    -Real.log (989468930359 / 1000000000000) ≤ (5293457 / 500000000) := by
  have h := checkLog_sound (w := (10531069641 / 1989468930359)) (n := 12)
    (lo := (10586913 / 1000000000)) (hi := (5293457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989468930359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989468930359) = 1/(989468930359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7061 : Bounds (-5293457 / 500000000) (-10586913 / 1000000000) (Real.log (989468930359 / 1000000000000)) := by
  have h := reflection_log_7061_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7062_neg : (5245961 / 500000000) ≤ -Real.log (247390731439 / 250000000000) ∧
    -Real.log (247390731439 / 250000000000) ≤ (10491923 / 1000000000) := by
  have h := checkLog_sound (w := (2609268561 / 497390731439)) (n := 12)
    (lo := (5245961 / 500000000)) (hi := (10491923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247390731439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247390731439) = 1/(247390731439 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7062 : Bounds (-10491923 / 1000000000) (-5245961 / 500000000) (Real.log (247390731439 / 250000000000)) := by
  have h := reflection_log_7062_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7063_neg : (205039333 / 1000000000) ≤ -Real.log (50000000000 / 61378667421) ∧
    -Real.log (50000000000 / 61378667421) ≤ (102519667 / 500000000) := by
  have h := checkLog_sound (w := (11378667421 / 111378667421)) (n := 12)
    (lo := (205039333 / 1000000000)) (hi := (102519667 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61378667421 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61378667421 / 50000000000) = 1/(50000000000 / 61378667421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7063 : Bounds (205039333 / 1000000000) (102519667 / 500000000) (Real.log (61378667421 / 50000000000)) := by
  have h := reflection_log_7063_neg
  have he : Real.log (61378667421 / 50000000000) = -Real.log (50000000000 / 61378667421) := by
    rw [show ((61378667421 / 50000000000) : ℝ) = ((50000000000 / 61378667421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7064_neg : (205967059 / 1000000000) ≤ -Real.log (1562500000 / 1919863639) ∧
    -Real.log (1562500000 / 1919863639) ≤ (10298353 / 50000000) := by
  have h := checkLog_sound (w := (357363639 / 3482363639)) (n := 12)
    (lo := (205967059 / 1000000000)) (hi := (10298353 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1919863639 / 1562500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1919863639 / 1562500000) = 1/(1562500000 / 1919863639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7064 : Bounds (205967059 / 1000000000) (10298353 / 50000000) (Real.log (1919863639 / 1562500000)) := by
  have h := reflection_log_7064_neg
  have he : Real.log (1919863639 / 1562500000) = -Real.log (1562500000 / 1919863639) := by
    rw [show ((1919863639 / 1562500000) : ℝ) = ((1562500000 / 1919863639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7065_neg : (411719037 / 1000000000) ≤ -Real.log (500000000000 / 754705144291) ∧
    -Real.log (500000000000 / 754705144291) ≤ (205859519 / 500000000) := by
  have h := checkLog_sound (w := (254705144291 / 1254705144291)) (n := 12)
    (lo := (411719037 / 1000000000)) (hi := (205859519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((754705144291 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(754705144291 / 500000000000) = 1/(500000000000 / 754705144291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7065 : Bounds (411719037 / 1000000000) (205859519 / 500000000) (Real.log (754705144291 / 500000000000)) := by
  have h := reflection_log_7065_neg
  have he : Real.log (754705144291 / 500000000000) = -Real.log (500000000000 / 754705144291) := by
    rw [show ((754705144291 / 500000000000) : ℝ) = ((500000000000 / 754705144291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7066_neg : (412762127 / 1000000000) ≤ -Real.log (500000000000 / 755492780917) ∧
    -Real.log (500000000000 / 755492780917) ≤ (25797633 / 62500000) := by
  have h := checkLog_sound (w := (255492780917 / 1255492780917)) (n := 12)
    (lo := (412762127 / 1000000000)) (hi := (25797633 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((755492780917 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(755492780917 / 500000000000) = 1/(500000000000 / 755492780917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7066 : Bounds (412762127 / 1000000000) (25797633 / 62500000) (Real.log (755492780917 / 500000000000)) := by
  have h := reflection_log_7066_neg
  have he : Real.log (755492780917 / 500000000000) = -Real.log (500000000000 / 755492780917) := by
    rw [show ((755492780917 / 500000000000) : ℝ) = ((500000000000 / 755492780917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7067_neg : (92824673 / 500000000) ≤ -Real.log (250 / 301) ∧
    -Real.log (250 / 301) ≤ (185649347 / 1000000000) := by
  have h := checkLog_sound (w := (51 / 551)) (n := 12)
    (lo := (92824673 / 500000000)) (hi := (185649347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301 / 250) = 1/(250 / 301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7067 : Bounds (92824673 / 500000000) (185649347 / 1000000000) (Real.log (301 / 250)) := by
  have h := reflection_log_7067_neg
  have he : Real.log (301 / 250) = -Real.log (250 / 301) := by
    rw [show ((301 / 250) : ℝ) = ((250 / 301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7068_neg : (228156093 / 1000000000) ≤ -Real.log (199 / 250) ∧
    -Real.log (199 / 250) ≤ (114078047 / 500000000) := by
  have h := checkLog_sound (w := (51 / 449)) (n := 12)
    (lo := (228156093 / 1000000000)) (hi := (114078047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 199) = 1/(199 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7068 : Bounds (-114078047 / 500000000) (-228156093 / 1000000000) (Real.log (199 / 250)) := by
  have h := reflection_log_7068_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7069_neg : (203979 / 1000000000) ≤ -Real.log (250000 / 250051) ∧
    -Real.log (250000 / 250051) ≤ (10199 / 50000000) := by
  have h := checkLog_sound (w := (51 / 500051)) (n := 12)
    (lo := (203979 / 1000000000)) (hi := (10199 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250051 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250051 / 250000) = 1/(250000 / 250051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7069 : Bounds (203979 / 1000000000) (10199 / 50000000) (Real.log (250051 / 250000)) := by
  have h := reflection_log_7069_neg
  have he : Real.log (250051 / 250000) = -Real.log (250000 / 250051) := by
    rw [show ((250051 / 250000) : ℝ) = ((250000 / 250051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7070_neg : (10201 / 50000000) ≤ -Real.log (249949 / 250000) ∧
    -Real.log (249949 / 250000) ≤ (204021 / 1000000000) := by
  have h := checkLog_sound (w := (51 / 499949)) (n := 12)
    (lo := (10201 / 50000000)) (hi := (204021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249949) = 1/(249949 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7070 : Bounds (-204021 / 1000000000) (-10201 / 50000000) (Real.log (249949 / 250000)) := by
  have h := reflection_log_7070_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7071_neg : (97505949 / 1000000000) ≤ -Real.log (500000 / 551209) ∧
    -Real.log (500000 / 551209) ≤ (1950119 / 20000000) := by
  have h := checkLog_sound (w := (51209 / 1051209)) (n := 12)
    (lo := (97505949 / 1000000000)) (hi := (1950119 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((551209 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(551209 / 500000) = 1/(500000 / 551209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7071 : Bounds (97505949 / 1000000000) (1950119 / 20000000) (Real.log (551209 / 500000)) := by
  have h := reflection_log_7071_neg
  have he : Real.log (551209 / 500000) = -Real.log (500000 / 551209) := by
    rw [show ((551209 / 500000) : ℝ) = ((500000 / 551209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7072_neg : (108050797 / 1000000000) ≤ -Real.log (448791 / 500000) ∧
    -Real.log (448791 / 500000) ≤ (54025399 / 500000000) := by
  have h := checkLog_sound (w := (51209 / 948791)) (n := 12)
    (lo := (108050797 / 1000000000)) (hi := (54025399 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 448791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 448791) = 1/(448791 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7072 : Bounds (-54025399 / 500000000) (-108050797 / 1000000000) (Real.log (448791 / 500000)) := by
  have h := reflection_log_7072_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7073_neg : (4896111 / 50000000) ≤ -Real.log (1000000 / 1102877) ∧
    -Real.log (1000000 / 1102877) ≤ (97922221 / 1000000000) := by
  have h := checkLog_sound (w := (102877 / 2102877)) (n := 12)
    (lo := (4896111 / 50000000)) (hi := (97922221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1102877 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1102877 / 1000000) = 1/(1000000 / 1102877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7073 : Bounds (4896111 / 50000000) (97922221 / 1000000000) (Real.log (1102877 / 1000000)) := by
  have h := reflection_log_7073_neg
  have he : Real.log (1102877 / 1000000) = -Real.log (1000000 / 1102877) := by
    rw [show ((1102877 / 1000000) : ℝ) = ((1000000 / 1102877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7074_neg : (54281151 / 500000000) ≤ -Real.log (897123 / 1000000) ∧
    -Real.log (897123 / 1000000) ≤ (108562303 / 1000000000) := by
  have h := checkLog_sound (w := (102877 / 1897123)) (n := 12)
    (lo := (54281151 / 500000000)) (hi := (108562303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 897123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 897123) = 1/(897123 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7074 : Bounds (-108562303 / 1000000000) (-54281151 / 500000000) (Real.log (897123 / 1000000)) := by
  have h := reflection_log_7074_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7075_neg : (5320041 / 500000000) ≤ -Real.log (989416322871 / 1000000000000) ∧
    -Real.log (989416322871 / 1000000000000) ≤ (10640083 / 1000000000) := by
  have h := checkLog_sound (w := (10583677129 / 1989416322871)) (n := 12)
    (lo := (5320041 / 500000000)) (hi := (10640083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989416322871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989416322871) = 1/(989416322871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7075 : Bounds (-10640083 / 1000000000) (-5320041 / 500000000) (Real.log (989416322871 / 1000000000000)) := by
  have h := reflection_log_7075_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7076_neg : (659053 / 62500000) ≤ -Real.log (247377638319 / 250000000000) ∧
    -Real.log (247377638319 / 250000000000) ≤ (10544849 / 1000000000) := by
  have h := checkLog_sound (w := (2622361681 / 497377638319)) (n := 12)
    (lo := (659053 / 62500000)) (hi := (10544849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247377638319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247377638319) = 1/(247377638319 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7076 : Bounds (-10544849 / 1000000000) (-659053 / 62500000) (Real.log (247377638319 / 250000000000)) := by
  have h := reflection_log_7076_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7077_neg : (205556747 / 1000000000) ≤ -Real.log (500000000000 / 614104338099) ∧
    -Real.log (500000000000 / 614104338099) ≤ (51389187 / 250000000) := by
  have h := checkLog_sound (w := (114104338099 / 1114104338099)) (n := 12)
    (lo := (205556747 / 1000000000)) (hi := (51389187 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((614104338099 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(614104338099 / 500000000000) = 1/(500000000000 / 614104338099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7077 : Bounds (205556747 / 1000000000) (51389187 / 250000000) (Real.log (614104338099 / 500000000000)) := by
  have h := reflection_log_7077_neg
  have he : Real.log (614104338099 / 500000000000) = -Real.log (500000000000 / 614104338099) := by
    rw [show ((614104338099 / 500000000000) : ℝ) = ((500000000000 / 614104338099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7078_neg : (103242261 / 500000000) ≤ -Real.log (250000000000 / 307337176731) ∧
    -Real.log (250000000000 / 307337176731) ≤ (206484523 / 1000000000) := by
  have h := checkLog_sound (w := (57337176731 / 557337176731)) (n := 12)
    (lo := (103242261 / 500000000)) (hi := (206484523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307337176731 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307337176731 / 250000000000) = 1/(250000000000 / 307337176731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7078 : Bounds (103242261 / 500000000) (206484523 / 1000000000) (Real.log (307337176731 / 250000000000)) := by
  have h := reflection_log_7078_neg
  have he : Real.log (307337176731 / 250000000000) = -Real.log (250000000000 / 307337176731) := by
    rw [show ((307337176731 / 250000000000) : ℝ) = ((250000000000 / 307337176731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7079_neg : (412762127 / 1000000000) ≤ -Real.log (125000000000 / 188873195229) ∧
    -Real.log (125000000000 / 188873195229) ≤ (25797633 / 62500000) := by
  have h := checkLog_sound (w := (63873195229 / 313873195229)) (n := 12)
    (lo := (412762127 / 1000000000)) (hi := (25797633 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((188873195229 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(188873195229 / 125000000000) = 1/(125000000000 / 188873195229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7079 : Bounds (412762127 / 1000000000) (25797633 / 62500000) (Real.log (188873195229 / 125000000000)) := by
  have h := reflection_log_7079_neg
  have he : Real.log (188873195229 / 125000000000) = -Real.log (125000000000 / 188873195229) := by
    rw [show ((188873195229 / 125000000000) : ℝ) = ((125000000000 / 188873195229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7080_neg : (646571 / 1562500) ≤ -Real.log (125000000000 / 189070351759) ∧
    -Real.log (125000000000 / 189070351759) ≤ (413805441 / 1000000000) := by
  have h := checkLog_sound (w := (64070351759 / 314070351759)) (n := 12)
    (lo := (646571 / 1562500)) (hi := (413805441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((189070351759 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(189070351759 / 125000000000) = 1/(125000000000 / 189070351759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7080 : Bounds (646571 / 1562500) (413805441 / 1000000000) (Real.log (189070351759 / 125000000000)) := by
  have h := reflection_log_7080_neg
  have he : Real.log (189070351759 / 125000000000) = -Real.log (125000000000 / 189070351759) := by
    rw [show ((189070351759 / 125000000000) : ℝ) = ((125000000000 / 189070351759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7081_neg : (186064543 / 1000000000) ≤ -Real.log (2000 / 2409) ∧
    -Real.log (2000 / 2409) ≤ (5814517 / 31250000) := by
  have h := checkLog_sound (w := (409 / 4409)) (n := 12)
    (lo := (186064543 / 1000000000)) (hi := (5814517 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2409 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2409 / 2000) = 1/(2000 / 2409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7081 : Bounds (186064543 / 1000000000) (5814517 / 31250000) (Real.log (2409 / 2000)) := by
  have h := reflection_log_7081_neg
  have he : Real.log (2409 / 2000) = -Real.log (2000 / 2409) := by
    rw [show ((2409 / 2000) : ℝ) = ((2000 / 2409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7082_neg : (228784431 / 1000000000) ≤ -Real.log (1591 / 2000) ∧
    -Real.log (1591 / 2000) ≤ (14299027 / 62500000) := by
  have h := checkLog_sound (w := (409 / 3591)) (n := 12)
    (lo := (228784431 / 1000000000)) (hi := (14299027 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1591) = 1/(1591 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7082 : Bounds (-14299027 / 62500000) (-228784431 / 1000000000) (Real.log (1591 / 2000)) := by
  have h := reflection_log_7082_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7083_neg : (204479 / 1000000000) ≤ -Real.log (2000000 / 2000409) ∧
    -Real.log (2000000 / 2000409) ≤ (639 / 3125000) := by
  have h := checkLog_sound (w := (409 / 4000409)) (n := 12)
    (lo := (204479 / 1000000000)) (hi := (639 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000409 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000409 / 2000000) = 1/(2000000 / 2000409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7083 : Bounds (204479 / 1000000000) (639 / 3125000) (Real.log (2000409 / 2000000)) := by
  have h := reflection_log_7083_neg
  have he : Real.log (2000409 / 2000000) = -Real.log (2000000 / 2000409) := by
    rw [show ((2000409 / 2000000) : ℝ) = ((2000000 / 2000409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7084_neg : (5113 / 25000000) ≤ -Real.log (1999591 / 2000000) ∧
    -Real.log (1999591 / 2000000) ≤ (204521 / 1000000000) := by
  have h := checkLog_sound (w := (409 / 3999591)) (n := 12)
    (lo := (5113 / 25000000)) (hi := (204521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999591) = 1/(1999591 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7084 : Bounds (-204521 / 1000000000) (-5113 / 25000000) (Real.log (1999591 / 2000000)) := by
  have h := reflection_log_7084_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7085_neg : (6108577 / 62500000) ≤ -Real.log (1000000 / 1102673) ∧
    -Real.log (1000000 / 1102673) ≤ (97737233 / 1000000000) := by
  have h := checkLog_sound (w := (102673 / 2102673)) (n := 12)
    (lo := (6108577 / 62500000)) (hi := (97737233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1102673 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1102673 / 1000000) = 1/(1000000 / 1102673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7085 : Bounds (6108577 / 62500000) (97737233 / 1000000000) (Real.log (1102673 / 1000000)) := by
  have h := reflection_log_7085_neg
  have he : Real.log (1102673 / 1000000) = -Real.log (1000000 / 1102673) := by
    rw [show ((1102673 / 1000000) : ℝ) = ((1000000 / 1102673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7086_neg : (54167467 / 500000000) ≤ -Real.log (897327 / 1000000) ∧
    -Real.log (897327 / 1000000) ≤ (21666987 / 200000000) := by
  have h := checkLog_sound (w := (102673 / 1897327)) (n := 12)
    (lo := (54167467 / 500000000)) (hi := (21666987 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 897327) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 897327) = 1/(897327 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7086 : Bounds (-21666987 / 200000000) (-54167467 / 500000000) (Real.log (897327 / 1000000)) := by
  have h := reflection_log_7086_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7087_neg : (98154313 / 1000000000) ≤ -Real.log (1000000 / 1103133) ∧
    -Real.log (1000000 / 1103133) ≤ (49077157 / 500000000) := by
  have h := checkLog_sound (w := (103133 / 2103133)) (n := 12)
    (lo := (98154313 / 1000000000)) (hi := (49077157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1103133 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1103133 / 1000000) = 1/(1000000 / 1103133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7087 : Bounds (98154313 / 1000000000) (49077157 / 500000000) (Real.log (1103133 / 1000000)) := by
  have h := reflection_log_7087_neg
  have he : Real.log (1103133 / 1000000) = -Real.log (1000000 / 1103133) := by
    rw [show ((1103133 / 1000000) : ℝ) = ((1000000 / 1103133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7088_neg : (108847699 / 1000000000) ≤ -Real.log (896867 / 1000000) ∧
    -Real.log (896867 / 1000000) ≤ (1088477 / 10000000) := by
  have h := checkLog_sound (w := (103133 / 1896867)) (n := 12)
    (lo := (108847699 / 1000000000)) (hi := (1088477 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 896867) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 896867) = 1/(896867 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7088 : Bounds (-1088477 / 10000000) (-108847699 / 1000000000) (Real.log (896867 / 1000000)) := by
  have h := reflection_log_7088_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7089_neg : (5346693 / 500000000) ≤ -Real.log (989363584311 / 1000000000000) ∧
    -Real.log (989363584311 / 1000000000000) ≤ (10693387 / 1000000000) := by
  have h := checkLog_sound (w := (10636415689 / 1989363584311)) (n := 12)
    (lo := (5346693 / 500000000)) (hi := (10693387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989363584311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989363584311) = 1/(989363584311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7089 : Bounds (-10693387 / 1000000000) (-5346693 / 500000000) (Real.log (989363584311 / 1000000000000)) := by
  have h := reflection_log_7089_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7090_neg : (5298851 / 500000000) ≤ -Real.log (989458255071 / 1000000000000) ∧
    -Real.log (989458255071 / 1000000000000) ≤ (10597703 / 1000000000) := by
  have h := checkLog_sound (w := (10541744929 / 1989458255071)) (n := 12)
    (lo := (5298851 / 500000000)) (hi := (10597703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989458255071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989458255071) = 1/(989458255071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7090 : Bounds (-10597703 / 1000000000) (-5298851 / 500000000) (Real.log (989458255071 / 1000000000000)) := by
  have h := reflection_log_7090_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7091_neg : (103036083 / 500000000) ≤ -Real.log (250000000000 / 307210470653) ∧
    -Real.log (250000000000 / 307210470653) ≤ (206072167 / 1000000000) := by
  have h := checkLog_sound (w := (57210470653 / 557210470653)) (n := 12)
    (lo := (103036083 / 500000000)) (hi := (206072167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307210470653 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(307210470653 / 250000000000) = 1/(250000000000 / 307210470653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7091 : Bounds (103036083 / 500000000) (206072167 / 1000000000) (Real.log (307210470653 / 250000000000)) := by
  have h := reflection_log_7091_neg
  have he : Real.log (307210470653 / 250000000000) = -Real.log (250000000000 / 307210470653) := by
    rw [show ((307210470653 / 250000000000) : ℝ) = ((250000000000 / 307210470653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7092_neg : (207002013 / 1000000000) ≤ -Real.log (62500000000 / 76874065497) ∧
    -Real.log (62500000000 / 76874065497) ≤ (103501007 / 500000000) := by
  have h := checkLog_sound (w := (14374065497 / 139374065497)) (n := 12)
    (lo := (207002013 / 1000000000)) (hi := (103501007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76874065497 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76874065497 / 62500000000) = 1/(62500000000 / 76874065497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7092 : Bounds (207002013 / 1000000000) (103501007 / 500000000) (Real.log (76874065497 / 62500000000)) := by
  have h := reflection_log_7092_neg
  have he : Real.log (76874065497 / 62500000000) = -Real.log (62500000000 / 76874065497) := by
    rw [show ((76874065497 / 62500000000) : ℝ) = ((62500000000 / 76874065497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7093_neg : (646571 / 1562500) ≤ -Real.log (100000000000 / 151256281407) ∧
    -Real.log (100000000000 / 151256281407) ≤ (413805441 / 1000000000) := by
  have h := checkLog_sound (w := (51256281407 / 251256281407)) (n := 12)
    (lo := (646571 / 1562500)) (hi := (413805441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151256281407 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151256281407 / 100000000000) = 1/(100000000000 / 151256281407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7093 : Bounds (646571 / 1562500) (413805441 / 1000000000) (Real.log (151256281407 / 100000000000)) := by
  have h := reflection_log_7093_neg
  have he : Real.log (151256281407 / 100000000000) = -Real.log (100000000000 / 151256281407) := by
    rw [show ((151256281407 / 100000000000) : ℝ) = ((100000000000 / 151256281407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7094_neg : (207424487 / 500000000) ≤ -Real.log (500000000000 / 757071024513) ∧
    -Real.log (500000000000 / 757071024513) ≤ (16593959 / 40000000) := by
  have h := checkLog_sound (w := (257071024513 / 1257071024513)) (n := 12)
    (lo := (207424487 / 500000000)) (hi := (16593959 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((757071024513 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(757071024513 / 500000000000) = 1/(500000000000 / 757071024513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7094 : Bounds (207424487 / 500000000) (16593959 / 40000000) (Real.log (757071024513 / 500000000000)) := by
  have h := reflection_log_7094_neg
  have he : Real.log (757071024513 / 500000000000) = -Real.log (500000000000 / 757071024513) := by
    rw [show ((757071024513 / 500000000000) : ℝ) = ((500000000000 / 757071024513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7095_neg : (93239783 / 500000000) ≤ -Real.log (200 / 241) ∧
    -Real.log (200 / 241) ≤ (186479567 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 441)) (n := 12)
    (lo := (93239783 / 500000000)) (hi := (186479567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(241 / 200) = 1/(200 / 241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7095 : Bounds (93239783 / 500000000) (186479567 / 1000000000) (Real.log (241 / 200)) := by
  have h := reflection_log_7095_neg
  have he : Real.log (241 / 200) = -Real.log (200 / 241) := by
    rw [show ((241 / 200) : ℝ) = ((200 / 241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7096_neg : (57353291 / 250000000) ≤ -Real.log (159 / 200) ∧
    -Real.log (159 / 200) ≤ (45882633 / 200000000) := by
  have h := checkLog_sound (w := (41 / 359)) (n := 12)
    (lo := (57353291 / 250000000)) (hi := (45882633 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 159) = 1/(159 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7096 : Bounds (-45882633 / 200000000) (-57353291 / 250000000) (Real.log (159 / 200)) := by
  have h := reflection_log_7096_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7097_neg : (102489 / 500000000) ≤ -Real.log (200000 / 200041) ∧
    -Real.log (200000 / 200041) ≤ (204979 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 400041)) (n := 12)
    (lo := (102489 / 500000000)) (hi := (204979 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200041 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200041 / 200000) = 1/(200000 / 200041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7097 : Bounds (102489 / 500000000) (204979 / 1000000000) (Real.log (200041 / 200000)) := by
  have h := reflection_log_7097_neg
  have he : Real.log (200041 / 200000) = -Real.log (200000 / 200041) := by
    rw [show ((200041 / 200000) : ℝ) = ((200000 / 200041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7098_neg : (205021 / 1000000000) ≤ -Real.log (199959 / 200000) ∧
    -Real.log (199959 / 200000) ≤ (102511 / 500000000) := by
  have h := checkLog_sound (w := (41 / 399959)) (n := 12)
    (lo := (205021 / 1000000000)) (hi := (102511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199959) = 1/(199959 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7098 : Bounds (-102511 / 500000000) (-205021 / 1000000000) (Real.log (199959 / 200000)) := by
  have h := reflection_log_7098_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7099_neg : (12246171 / 125000000) ≤ -Real.log (1000000 / 1102929) ∧
    -Real.log (1000000 / 1102929) ≤ (97969369 / 1000000000) := by
  have h := checkLog_sound (w := (102929 / 2102929)) (n := 12)
    (lo := (12246171 / 125000000)) (hi := (97969369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1102929 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1102929 / 1000000) = 1/(1000000 / 1102929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7099 : Bounds (12246171 / 125000000) (97969369 / 1000000000) (Real.log (1102929 / 1000000)) := by
  have h := reflection_log_7099_neg
  have he : Real.log (1102929 / 1000000) = -Real.log (1000000 / 1102929) := by
    rw [show ((1102929 / 1000000) : ℝ) = ((1000000 / 1102929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7100_neg : (108620267 / 1000000000) ≤ -Real.log (897071 / 1000000) ∧
    -Real.log (897071 / 1000000) ≤ (27155067 / 250000000) := by
  have h := checkLog_sound (w := (102929 / 1897071)) (n := 12)
    (lo := (108620267 / 1000000000)) (hi := (27155067 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 897071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 897071) = 1/(897071 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7100 : Bounds (-27155067 / 250000000) (-108620267 / 1000000000) (Real.log (897071 / 1000000)) := by
  have h := reflection_log_7100_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7101_neg : (6149147 / 62500000) ≤ -Real.log (1000000 / 1103389) ∧
    -Real.log (1000000 / 1103389) ≤ (98386353 / 1000000000) := by
  have h := checkLog_sound (w := (103389 / 2103389)) (n := 12)
    (lo := (6149147 / 62500000)) (hi := (98386353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1103389 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1103389 / 1000000) = 1/(1000000 / 1103389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7101 : Bounds (6149147 / 62500000) (98386353 / 1000000000) (Real.log (1103389 / 1000000)) := by
  have h := reflection_log_7101_neg
  have he : Real.log (1103389 / 1000000) = -Real.log (1000000 / 1103389) := by
    rw [show ((1103389 / 1000000) : ℝ) = ((1000000 / 1103389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7102_neg : (54566589 / 500000000) ≤ -Real.log (896611 / 1000000) ∧
    -Real.log (896611 / 1000000) ≤ (109133179 / 1000000000) := by
  have h := checkLog_sound (w := (103389 / 1896611)) (n := 12)
    (lo := (54566589 / 500000000)) (hi := (109133179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 896611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 896611) = 1/(896611 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7102 : Bounds (-109133179 / 1000000000) (-54566589 / 500000000) (Real.log (896611 / 1000000)) := by
  have h := reflection_log_7102_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7103_neg : (5373413 / 500000000) ≤ -Real.log (989310714679 / 1000000000000) ∧
    -Real.log (989310714679 / 1000000000000) ≤ (10746827 / 1000000000) := by
  have h := checkLog_sound (w := (10689285321 / 1989310714679)) (n := 12)
    (lo := (5373413 / 500000000)) (hi := (10746827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 989310714679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 989310714679) = 1/(989310714679 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7103 : Bounds (-10746827 / 1000000000) (-5373413 / 500000000) (Real.log (989310714679 / 1000000000000)) := by
  have h := reflection_log_7103_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
