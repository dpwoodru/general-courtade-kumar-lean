import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2240_neg : (181881653 / 1000000000) ≤ -Real.log (8337 / 10000) ∧
    -Real.log (8337 / 10000) ≤ (90940827 / 500000000) := by
  have h := checkLog_sound (w := (1663 / 18337)) (n := 12)
    (lo := (181881653 / 1000000000)) (hi := (90940827 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8337) = 1/(8337 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2240 : Bounds (-90940827 / 500000000) (-181881653 / 1000000000) (Real.log (8337 / 10000)) := by
  have h := reflection_log_2240_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2241_neg : (83143 / 500000000) ≤ -Real.log (10000000 / 10001663) ∧
    -Real.log (10000000 / 10001663) ≤ (166287 / 1000000000) := by
  have h := checkLog_sound (w := (1663 / 20001663)) (n := 12)
    (lo := (83143 / 500000000)) (hi := (166287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001663 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001663 / 10000000) = 1/(10000000 / 10001663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2241 : Bounds (83143 / 500000000) (166287 / 1000000000) (Real.log (10001663 / 10000000)) := by
  have h := reflection_log_2241_neg
  have he : Real.log (10001663 / 10000000) = -Real.log (10000000 / 10001663) := by
    rw [show ((10001663 / 10000000) : ℝ) = ((10000000 / 10001663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2242_neg : (166313 / 1000000000) ≤ -Real.log (9998337 / 10000000) ∧
    -Real.log (9998337 / 10000000) ≤ (83157 / 500000000) := by
  have h := checkLog_sound (w := (1663 / 19998337)) (n := 12)
    (lo := (166313 / 1000000000)) (hi := (83157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998337) = 1/(9998337 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2242 : Bounds (-83157 / 500000000) (-166313 / 1000000000) (Real.log (9998337 / 10000000)) := by
  have h := reflection_log_2242_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2243_neg : (40067813 / 500000000) ≤ -Real.log (500000 / 541717) ∧
    -Real.log (500000 / 541717) ≤ (80135627 / 1000000000) := by
  have h := checkLog_sound (w := (41717 / 1041717)) (n := 12)
    (lo := (40067813 / 500000000)) (hi := (80135627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541717 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541717 / 500000) = 1/(500000 / 541717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2243 : Bounds (40067813 / 500000000) (80135627 / 1000000000) (Real.log (541717 / 500000)) := by
  have h := reflection_log_2243_neg
  have he : Real.log (541717 / 500000) = -Real.log (500000 / 541717) := by
    rw [show ((541717 / 500000) : ℝ) = ((500000 / 541717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2244_neg : (87121201 / 1000000000) ≤ -Real.log (458283 / 500000) ∧
    -Real.log (458283 / 500000) ≤ (43560601 / 500000000) := by
  have h := checkLog_sound (w := (41717 / 958283)) (n := 12)
    (lo := (87121201 / 1000000000)) (hi := (43560601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458283) = 1/(458283 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2244 : Bounds (-43560601 / 500000000) (-87121201 / 1000000000) (Real.log (458283 / 500000)) := by
  have h := reflection_log_2244_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2245_neg : (16067179 / 200000000) ≤ -Real.log (1000000 / 1083651) ∧
    -Real.log (1000000 / 1083651) ≤ (10041987 / 125000000) := by
  have h := checkLog_sound (w := (83651 / 2083651)) (n := 12)
    (lo := (16067179 / 200000000)) (hi := (10041987 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083651 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083651 / 1000000) = 1/(1000000 / 1083651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2245 : Bounds (16067179 / 200000000) (10041987 / 125000000) (Real.log (1083651 / 1000000)) := by
  have h := reflection_log_2245_neg
  have he : Real.log (1083651 / 1000000) = -Real.log (1000000 / 1083651) := by
    rw [show ((1083651 / 1000000) : ℝ) = ((1000000 / 1083651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2246_neg : (43678991 / 500000000) ≤ -Real.log (916349 / 1000000) ∧
    -Real.log (916349 / 1000000) ≤ (87357983 / 1000000000) := by
  have h := checkLog_sound (w := (83651 / 1916349)) (n := 12)
    (lo := (43678991 / 500000000)) (hi := (87357983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916349) = 1/(916349 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2246 : Bounds (-87357983 / 1000000000) (-43678991 / 500000000) (Real.log (916349 / 1000000)) := by
  have h := reflection_log_2246_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2247_neg : (7022087 / 1000000000) ≤ -Real.log (993002510199 / 1000000000000) ∧
    -Real.log (993002510199 / 1000000000000) ≤ (877761 / 125000000) := by
  have h := checkLog_sound (w := (6997489801 / 1993002510199)) (n := 12)
    (lo := (7022087 / 1000000000)) (hi := (877761 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993002510199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993002510199) = 1/(993002510199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2247 : Bounds (-877761 / 125000000) (-7022087 / 1000000000) (Real.log (993002510199 / 1000000000000)) := by
  have h := reflection_log_2247_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2248_neg : (3492787 / 500000000) ≤ -Real.log (248259691911 / 250000000000) ∧
    -Real.log (248259691911 / 250000000000) ≤ (279423 / 40000000) := by
  have h := checkLog_sound (w := (1740308089 / 498259691911)) (n := 12)
    (lo := (3492787 / 500000000)) (hi := (279423 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248259691911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248259691911) = 1/(248259691911 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2248 : Bounds (-279423 / 40000000) (-3492787 / 500000000) (Real.log (248259691911 / 250000000000)) := by
  have h := reflection_log_2248_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2249_neg : (167256827 / 1000000000) ≤ -Real.log (500000000000 / 591028905719) ∧
    -Real.log (500000000000 / 591028905719) ≤ (41814207 / 250000000) := by
  have h := checkLog_sound (w := (91028905719 / 1091028905719)) (n := 12)
    (lo := (167256827 / 1000000000)) (hi := (41814207 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591028905719 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591028905719 / 500000000000) = 1/(500000000000 / 591028905719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2249 : Bounds (167256827 / 1000000000) (41814207 / 250000000) (Real.log (591028905719 / 500000000000)) := by
  have h := reflection_log_2249_neg
  have he : Real.log (591028905719 / 500000000000) = -Real.log (500000000000 / 591028905719) := by
    rw [show ((591028905719 / 500000000000) : ℝ) = ((500000000000 / 591028905719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2250_neg : (167693877 / 1000000000) ≤ -Real.log (500000000000 / 591287271553) ∧
    -Real.log (500000000000 / 591287271553) ≤ (83846939 / 500000000) := by
  have h := checkLog_sound (w := (91287271553 / 1091287271553)) (n := 12)
    (lo := (167693877 / 1000000000)) (hi := (83846939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591287271553 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591287271553 / 500000000000) = 1/(500000000000 / 591287271553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2250 : Bounds (167693877 / 1000000000) (83846939 / 500000000) (Real.log (591287271553 / 500000000000)) := by
  have h := reflection_log_2250_neg
  have he : Real.log (591287271553 / 500000000000) = -Real.log (500000000000 / 591287271553) := by
    rw [show ((591287271553 / 500000000000) : ℝ) = ((500000000000 / 591287271553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2251_neg : (335512313 / 1000000000) ≤ -Real.log (500000000000 / 699328376109) ∧
    -Real.log (500000000000 / 699328376109) ≤ (167756157 / 500000000) := by
  have h := checkLog_sound (w := (199328376109 / 1199328376109)) (n := 12)
    (lo := (335512313 / 1000000000)) (hi := (167756157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699328376109 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699328376109 / 500000000000) = 1/(500000000000 / 699328376109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2251 : Bounds (335512313 / 1000000000) (167756157 / 500000000) (Real.log (699328376109 / 500000000000)) := by
  have h := reflection_log_2251_neg
  have he : Real.log (699328376109 / 500000000000) = -Real.log (500000000000 / 699328376109) := by
    rw [show ((699328376109 / 500000000000) : ℝ) = ((500000000000 / 699328376109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2252_neg : (167858999 / 500000000) ≤ -Real.log (250000000000 / 349736116109) ∧
    -Real.log (250000000000 / 349736116109) ≤ (335717999 / 1000000000) := by
  have h := checkLog_sound (w := (99736116109 / 599736116109)) (n := 12)
    (lo := (167858999 / 500000000)) (hi := (335717999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349736116109 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(349736116109 / 250000000000) = 1/(250000000000 / 349736116109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2252 : Bounds (167858999 / 500000000) (335717999 / 1000000000) (Real.log (349736116109 / 250000000000)) := by
  have h := reflection_log_2252_neg
  have he : Real.log (349736116109 / 250000000000) = -Real.log (250000000000 / 349736116109) := by
    rw [show ((349736116109 / 250000000000) : ℝ) = ((250000000000 / 349736116109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2253_neg : (76961041 / 500000000) ≤ -Real.log (625 / 729) ∧
    -Real.log (625 / 729) ≤ (153922083 / 1000000000) := by
  have h := checkLog_sound (w := (52 / 677)) (n := 12)
    (lo := (76961041 / 500000000)) (hi := (153922083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729 / 625) = 1/(625 / 729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2253 : Bounds (76961041 / 500000000) (153922083 / 1000000000) (Real.log (729 / 625)) := by
  have h := reflection_log_2253_neg
  have he : Real.log (729 / 625) = -Real.log (625 / 729) := by
    rw [show ((729 / 625) : ℝ) = ((625 / 729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2254_neg : (182001607 / 1000000000) ≤ -Real.log (521 / 625) ∧
    -Real.log (521 / 625) ≤ (22750201 / 125000000) := by
  have h := checkLog_sound (w := (52 / 573)) (n := 12)
    (lo := (182001607 / 1000000000)) (hi := (22750201 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 521) = 1/(521 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2254 : Bounds (-22750201 / 125000000) (-182001607 / 1000000000) (Real.log (521 / 625)) := by
  have h := reflection_log_2254_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2255_neg : (83193 / 500000000) ≤ -Real.log (78125 / 78138) ∧
    -Real.log (78125 / 78138) ≤ (166387 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 156263)) (n := 12)
    (lo := (83193 / 500000000)) (hi := (166387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78138 / 78125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78138 / 78125) = 1/(78125 / 78138) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2255 : Bounds (83193 / 500000000) (166387 / 1000000000) (Real.log (78138 / 78125)) := by
  have h := reflection_log_2255_neg
  have he : Real.log (78138 / 78125) = -Real.log (78125 / 78138) := by
    rw [show ((78138 / 78125) : ℝ) = ((78125 / 78138) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2256_neg : (166413 / 1000000000) ≤ -Real.log (78112 / 78125) ∧
    -Real.log (78112 / 78125) ≤ (83207 / 500000000) := by
  have h := checkLog_sound (w := (13 / 156237)) (n := 12)
    (lo := (166413 / 1000000000)) (hi := (83207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78125 / 78112) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78125 / 78112) = 1/(78112 / 78125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2256 : Bounds (-83207 / 500000000) (-166413 / 1000000000) (Real.log (78112 / 78125)) := by
  have h := reflection_log_2256_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2257_neg : (80182697 / 1000000000) ≤ -Real.log (200000 / 216697) ∧
    -Real.log (200000 / 216697) ≤ (40091349 / 500000000) := by
  have h := checkLog_sound (w := (16697 / 416697)) (n := 12)
    (lo := (80182697 / 1000000000)) (hi := (40091349 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216697 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216697 / 200000) = 1/(200000 / 216697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2257 : Bounds (80182697 / 1000000000) (40091349 / 500000000) (Real.log (216697 / 200000)) := by
  have h := reflection_log_2257_neg
  have he : Real.log (216697 / 200000) = -Real.log (200000 / 216697) := by
    rw [show ((216697 / 200000) : ℝ) = ((200000 / 216697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2258_neg : (17435369 / 200000000) ≤ -Real.log (183303 / 200000) ∧
    -Real.log (183303 / 200000) ≤ (43588423 / 500000000) := by
  have h := checkLog_sound (w := (16697 / 383303)) (n := 12)
    (lo := (17435369 / 200000000)) (hi := (43588423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183303) = 1/(183303 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2258 : Bounds (-43588423 / 500000000) (-17435369 / 200000000) (Real.log (183303 / 200000)) := by
  have h := reflection_log_2258_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2259_neg : (80382957 / 1000000000) ≤ -Real.log (500000 / 541851) ∧
    -Real.log (500000 / 541851) ≤ (40191479 / 500000000) := by
  have h := checkLog_sound (w := (41851 / 1041851)) (n := 12)
    (lo := (80382957 / 1000000000)) (hi := (40191479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541851 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541851 / 500000) = 1/(500000 / 541851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2259 : Bounds (80382957 / 1000000000) (40191479 / 500000000) (Real.log (541851 / 500000)) := by
  have h := reflection_log_2259_neg
  have he : Real.log (541851 / 500000) = -Real.log (500000 / 541851) := by
    rw [show ((541851 / 500000) : ℝ) = ((500000 / 541851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2260_neg : (87413639 / 1000000000) ≤ -Real.log (458149 / 500000) ∧
    -Real.log (458149 / 500000) ≤ (2185341 / 25000000) := by
  have h := checkLog_sound (w := (41851 / 958149)) (n := 12)
    (lo := (87413639 / 1000000000)) (hi := (2185341 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458149) = 1/(458149 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2260 : Bounds (-2185341 / 25000000) (-87413639 / 1000000000) (Real.log (458149 / 500000)) := by
  have h := reflection_log_2260_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2261_neg : (3515341 / 500000000) ≤ -Real.log (248248493799 / 250000000000) ∧
    -Real.log (248248493799 / 250000000000) ≤ (7030683 / 1000000000) := by
  have h := checkLog_sound (w := (1751506201 / 498248493799)) (n := 12)
    (lo := (3515341 / 500000000)) (hi := (7030683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248248493799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248248493799) = 1/(248248493799 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2261 : Bounds (-7030683 / 1000000000) (-3515341 / 500000000) (Real.log (248248493799 / 250000000000)) := by
  have h := reflection_log_2261_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2262_neg : (6994147 / 1000000000) ≤ -Real.log (39721210191 / 40000000000) ∧
    -Real.log (39721210191 / 40000000000) ≤ (1748537 / 250000000) := by
  have h := checkLog_sound (w := (278789809 / 79721210191)) (n := 12)
    (lo := (6994147 / 1000000000)) (hi := (1748537 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39721210191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39721210191) = 1/(39721210191 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2262 : Bounds (-1748537 / 250000000) (-6994147 / 1000000000) (Real.log (39721210191 / 40000000000)) := by
  have h := reflection_log_2262_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2263_neg : (167359543 / 1000000000) ≤ -Real.log (100000000000 / 118217923329) ∧
    -Real.log (100000000000 / 118217923329) ≤ (20919943 / 125000000) := by
  have h := checkLog_sound (w := (18217923329 / 218217923329)) (n := 12)
    (lo := (167359543 / 1000000000)) (hi := (20919943 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118217923329 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118217923329 / 100000000000) = 1/(100000000000 / 118217923329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2263 : Bounds (167359543 / 1000000000) (20919943 / 125000000) (Real.log (118217923329 / 100000000000)) := by
  have h := reflection_log_2263_neg
  have he : Real.log (118217923329 / 100000000000) = -Real.log (100000000000 / 118217923329) := by
    rw [show ((118217923329 / 100000000000) : ℝ) = ((100000000000 / 118217923329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2264_neg : (167796597 / 1000000000) ≤ -Real.log (500000000000 / 591348011237) ∧
    -Real.log (500000000000 / 591348011237) ≤ (83898299 / 500000000) := by
  have h := checkLog_sound (w := (91348011237 / 1091348011237)) (n := 12)
    (lo := (167796597 / 1000000000)) (hi := (83898299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591348011237 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591348011237 / 500000000000) = 1/(500000000000 / 591348011237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2264 : Bounds (167796597 / 1000000000) (83898299 / 500000000) (Real.log (591348011237 / 500000000000)) := by
  have h := reflection_log_2264_neg
  have he : Real.log (591348011237 / 500000000000) = -Real.log (500000000000 / 591348011237) := by
    rw [show ((591348011237 / 500000000000) : ℝ) = ((500000000000 / 591348011237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2265_neg : (167858999 / 500000000) ≤ -Real.log (500000000000 / 699472232217) ∧
    -Real.log (500000000000 / 699472232217) ≤ (335717999 / 1000000000) := by
  have h := checkLog_sound (w := (199472232217 / 1199472232217)) (n := 12)
    (lo := (167858999 / 500000000)) (hi := (335717999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699472232217 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699472232217 / 500000000000) = 1/(500000000000 / 699472232217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2265 : Bounds (167858999 / 500000000) (335717999 / 1000000000) (Real.log (699472232217 / 500000000000)) := by
  have h := reflection_log_2265_neg
  have he : Real.log (699472232217 / 500000000000) = -Real.log (500000000000 / 699472232217) := by
    rw [show ((699472232217 / 500000000000) : ℝ) = ((500000000000 / 699472232217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2266_neg : (33592369 / 100000000) ≤ -Real.log (500000000000 / 699616122841) ∧
    -Real.log (500000000000 / 699616122841) ≤ (335923691 / 1000000000) := by
  have h := checkLog_sound (w := (199616122841 / 1199616122841)) (n := 12)
    (lo := (33592369 / 100000000)) (hi := (335923691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699616122841 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699616122841 / 500000000000) = 1/(500000000000 / 699616122841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2266 : Bounds (33592369 / 100000000) (335923691 / 1000000000) (Real.log (699616122841 / 500000000000)) := by
  have h := reflection_log_2266_neg
  have he : Real.log (699616122841 / 500000000000) = -Real.log (500000000000 / 699616122841) := by
    rw [show ((699616122841 / 500000000000) : ℝ) = ((500000000000 / 699616122841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2267_neg : (38501953 / 250000000) ≤ -Real.log (2000 / 2333) ∧
    -Real.log (2000 / 2333) ≤ (154007813 / 1000000000) := by
  have h := checkLog_sound (w := (333 / 4333)) (n := 12)
    (lo := (38501953 / 250000000)) (hi := (154007813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2333 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2333 / 2000) = 1/(2000 / 2333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2267 : Bounds (38501953 / 250000000) (154007813 / 1000000000) (Real.log (2333 / 2000)) := by
  have h := reflection_log_2267_neg
  have he : Real.log (2333 / 2000) = -Real.log (2000 / 2333) := by
    rw [show ((2333 / 2000) : ℝ) = ((2000 / 2333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2268_neg : (22765197 / 125000000) ≤ -Real.log (1667 / 2000) ∧
    -Real.log (1667 / 2000) ≤ (182121577 / 1000000000) := by
  have h := checkLog_sound (w := (333 / 3667)) (n := 12)
    (lo := (22765197 / 125000000)) (hi := (182121577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1667) = 1/(1667 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2268 : Bounds (-182121577 / 1000000000) (-22765197 / 125000000) (Real.log (1667 / 2000)) := by
  have h := reflection_log_2268_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2269_neg : (83243 / 500000000) ≤ -Real.log (2000000 / 2000333) ∧
    -Real.log (2000000 / 2000333) ≤ (166487 / 1000000000) := by
  have h := checkLog_sound (w := (333 / 4000333)) (n := 12)
    (lo := (83243 / 500000000)) (hi := (166487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000333 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000333 / 2000000) = 1/(2000000 / 2000333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2269 : Bounds (83243 / 500000000) (166487 / 1000000000) (Real.log (2000333 / 2000000)) := by
  have h := reflection_log_2269_neg
  have he : Real.log (2000333 / 2000000) = -Real.log (2000000 / 2000333) := by
    rw [show ((2000333 / 2000000) : ℝ) = ((2000000 / 2000333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2270_neg : (166513 / 1000000000) ≤ -Real.log (1999667 / 2000000) ∧
    -Real.log (1999667 / 2000000) ≤ (83257 / 500000000) := by
  have h := checkLog_sound (w := (333 / 3999667)) (n := 12)
    (lo := (166513 / 1000000000)) (hi := (83257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999667) = 1/(1999667 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2270 : Bounds (-83257 / 500000000) (-166513 / 1000000000) (Real.log (1999667 / 2000000)) := by
  have h := reflection_log_2270_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2271_neg : (80229767 / 1000000000) ≤ -Real.log (62500 / 67721) ∧
    -Real.log (62500 / 67721) ≤ (10028721 / 125000000) := by
  have h := checkLog_sound (w := (5221 / 130221)) (n := 12)
    (lo := (80229767 / 1000000000)) (hi := (10028721 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67721 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67721 / 62500) = 1/(62500 / 67721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2271 : Bounds (80229767 / 1000000000) (10028721 / 125000000) (Real.log (67721 / 62500)) := by
  have h := reflection_log_2271_neg
  have he : Real.log (67721 / 62500) = -Real.log (62500 / 67721) := by
    rw [show ((67721 / 62500) : ℝ) = ((62500 / 67721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2272_neg : (21808123 / 250000000) ≤ -Real.log (57279 / 62500) ∧
    -Real.log (57279 / 62500) ≤ (87232493 / 1000000000) := by
  have h := checkLog_sound (w := (5221 / 119779)) (n := 12)
    (lo := (21808123 / 250000000)) (hi := (87232493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 57279) = 1/(57279 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2272 : Bounds (-87232493 / 1000000000) (-21808123 / 250000000) (Real.log (57279 / 62500)) := by
  have h := reflection_log_2272_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2273_neg : (80430017 / 1000000000) ≤ -Real.log (1000000 / 1083753) ∧
    -Real.log (1000000 / 1083753) ≤ (40215009 / 500000000) := by
  have h := checkLog_sound (w := (83753 / 2083753)) (n := 12)
    (lo := (80430017 / 1000000000)) (hi := (40215009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083753 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083753 / 1000000) = 1/(1000000 / 1083753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2273 : Bounds (80430017 / 1000000000) (40215009 / 500000000) (Real.log (1083753 / 1000000)) := by
  have h := reflection_log_2273_neg
  have he : Real.log (1083753 / 1000000) = -Real.log (1000000 / 1083753) := by
    rw [show ((1083753 / 1000000) : ℝ) = ((1000000 / 1083753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2274_neg : (874693 / 10000000) ≤ -Real.log (916247 / 1000000) ∧
    -Real.log (916247 / 1000000) ≤ (87469301 / 1000000000) := by
  have h := checkLog_sound (w := (83753 / 1916247)) (n := 12)
    (lo := (874693 / 10000000)) (hi := (87469301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916247) = 1/(916247 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2274 : Bounds (-87469301 / 1000000000) (-874693 / 10000000) (Real.log (916247 / 1000000)) := by
  have h := reflection_log_2274_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2275_neg : (3519641 / 500000000) ≤ -Real.log (992985434991 / 1000000000000) ∧
    -Real.log (992985434991 / 1000000000000) ≤ (7039283 / 1000000000) := by
  have h := checkLog_sound (w := (7014565009 / 1992985434991)) (n := 12)
    (lo := (3519641 / 500000000)) (hi := (7039283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992985434991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992985434991) = 1/(992985434991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2275 : Bounds (-7039283 / 1000000000) (-3519641 / 500000000) (Real.log (992985434991 / 1000000000000)) := by
  have h := reflection_log_2275_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2276_neg : (280109 / 40000000) ≤ -Real.log (3878991159 / 3906250000) ∧
    -Real.log (3878991159 / 3906250000) ≤ (3501363 / 500000000) := by
  have h := checkLog_sound (w := (27258841 / 7785241159)) (n := 12)
    (lo := (280109 / 40000000)) (hi := (3501363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3878991159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3878991159) = 1/(3878991159 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2276 : Bounds (-3501363 / 500000000) (-280109 / 40000000) (Real.log (3878991159 / 3906250000)) := by
  have h := reflection_log_2276_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2277_neg : (167462259 / 1000000000) ≤ -Real.log (62500000000 / 73893791791) ∧
    -Real.log (62500000000 / 73893791791) ≤ (8373113 / 50000000) := by
  have h := checkLog_sound (w := (11393791791 / 136393791791)) (n := 12)
    (lo := (167462259 / 1000000000)) (hi := (8373113 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73893791791 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73893791791 / 62500000000) = 1/(62500000000 / 73893791791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2277 : Bounds (167462259 / 1000000000) (8373113 / 50000000) (Real.log (73893791791 / 62500000000)) := by
  have h := reflection_log_2277_neg
  have he : Real.log (73893791791 / 62500000000) = -Real.log (62500000000 / 73893791791) := by
    rw [show ((73893791791 / 62500000000) : ℝ) = ((62500000000 / 73893791791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2278_neg : (167899317 / 1000000000) ≤ -Real.log (500000000000 / 591408757683) ∧
    -Real.log (500000000000 / 591408757683) ≤ (83949659 / 500000000) := by
  have h := checkLog_sound (w := (91408757683 / 1091408757683)) (n := 12)
    (lo := (167899317 / 1000000000)) (hi := (83949659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591408757683 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591408757683 / 500000000000) = 1/(500000000000 / 591408757683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2278 : Bounds (167899317 / 1000000000) (83949659 / 500000000) (Real.log (591408757683 / 500000000000)) := by
  have h := reflection_log_2278_neg
  have he : Real.log (591408757683 / 500000000000) = -Real.log (500000000000 / 591408757683) := by
    rw [show ((591408757683 / 500000000000) : ℝ) = ((500000000000 / 591408757683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2279_neg : (33592369 / 100000000) ≤ -Real.log (12500000000 / 17490403071) ∧
    -Real.log (12500000000 / 17490403071) ≤ (335923691 / 1000000000) := by
  have h := checkLog_sound (w := (4990403071 / 29990403071)) (n := 12)
    (lo := (33592369 / 100000000)) (hi := (335923691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17490403071 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17490403071 / 12500000000) = 1/(12500000000 / 17490403071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2279 : Bounds (33592369 / 100000000) (335923691 / 1000000000) (Real.log (17490403071 / 12500000000)) := by
  have h := reflection_log_2279_neg
  have he : Real.log (17490403071 / 12500000000) = -Real.log (12500000000 / 17490403071) := by
    rw [show ((17490403071 / 12500000000) : ℝ) = ((12500000000 / 17490403071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2280_neg : (336129389 / 1000000000) ≤ -Real.log (500000000000 / 699760047991) ∧
    -Real.log (500000000000 / 699760047991) ≤ (33612939 / 100000000) := by
  have h := checkLog_sound (w := (199760047991 / 1199760047991)) (n := 12)
    (lo := (336129389 / 1000000000)) (hi := (33612939 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699760047991 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699760047991 / 500000000000) = 1/(500000000000 / 699760047991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2280 : Bounds (336129389 / 1000000000) (33612939 / 100000000) (Real.log (699760047991 / 500000000000)) := by
  have h := reflection_log_2280_neg
  have he : Real.log (699760047991 / 500000000000) = -Real.log (500000000000 / 699760047991) := by
    rw [show ((699760047991 / 500000000000) : ℝ) = ((500000000000 / 699760047991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2281_neg : (30818707 / 200000000) ≤ -Real.log (5000 / 5833) ∧
    -Real.log (5000 / 5833) ≤ (4815423 / 31250000) := by
  have h := checkLog_sound (w := (833 / 10833)) (n := 12)
    (lo := (30818707 / 200000000)) (hi := (4815423 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5833 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5833 / 5000) = 1/(5000 / 5833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2281 : Bounds (30818707 / 200000000) (4815423 / 31250000) (Real.log (5833 / 5000)) := by
  have h := reflection_log_2281_neg
  have he : Real.log (5833 / 5000) = -Real.log (5000 / 5833) := by
    rw [show ((5833 / 5000) : ℝ) = ((5000 / 5833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2282_neg : (182241559 / 1000000000) ≤ -Real.log (4167 / 5000) ∧
    -Real.log (4167 / 5000) ≤ (4556039 / 25000000) := by
  have h := checkLog_sound (w := (833 / 9167)) (n := 12)
    (lo := (182241559 / 1000000000)) (hi := (4556039 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4167) = 1/(4167 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2282 : Bounds (-4556039 / 25000000) (-182241559 / 1000000000) (Real.log (4167 / 5000)) := by
  have h := reflection_log_2282_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2283_neg : (83293 / 500000000) ≤ -Real.log (5000000 / 5000833) ∧
    -Real.log (5000000 / 5000833) ≤ (166587 / 1000000000) := by
  have h := checkLog_sound (w := (833 / 10000833)) (n := 12)
    (lo := (83293 / 500000000)) (hi := (166587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000833 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000833 / 5000000) = 1/(5000000 / 5000833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2283 : Bounds (83293 / 500000000) (166587 / 1000000000) (Real.log (5000833 / 5000000)) := by
  have h := reflection_log_2283_neg
  have he : Real.log (5000833 / 5000000) = -Real.log (5000000 / 5000833) := by
    rw [show ((5000833 / 5000000) : ℝ) = ((5000000 / 5000833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2284_neg : (166613 / 1000000000) ≤ -Real.log (4999167 / 5000000) ∧
    -Real.log (4999167 / 5000000) ≤ (83307 / 500000000) := by
  have h := checkLog_sound (w := (833 / 9999167)) (n := 12)
    (lo := (166613 / 1000000000)) (hi := (83307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999167) = 1/(4999167 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2284 : Bounds (-83307 / 500000000) (-166613 / 1000000000) (Real.log (4999167 / 5000000)) := by
  have h := reflection_log_2284_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2285_neg : (80275911 / 1000000000) ≤ -Real.log (500000 / 541793) ∧
    -Real.log (500000 / 541793) ≤ (10034489 / 125000000) := by
  have h := checkLog_sound (w := (41793 / 1041793)) (n := 12)
    (lo := (80275911 / 1000000000)) (hi := (10034489 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541793 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541793 / 500000) = 1/(500000 / 541793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2285 : Bounds (80275911 / 1000000000) (10034489 / 125000000) (Real.log (541793 / 500000)) := by
  have h := reflection_log_2285_neg
  have he : Real.log (541793 / 500000) = -Real.log (500000 / 541793) := by
    rw [show ((541793 / 500000) : ℝ) = ((500000 / 541793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2286_neg : (87287051 / 1000000000) ≤ -Real.log (458207 / 500000) ∧
    -Real.log (458207 / 500000) ≤ (21821763 / 250000000) := by
  have h := checkLog_sound (w := (41793 / 958207)) (n := 12)
    (lo := (87287051 / 1000000000)) (hi := (21821763 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458207) = 1/(458207 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2286 : Bounds (-21821763 / 250000000) (-87287051 / 1000000000) (Real.log (458207 / 500000)) := by
  have h := reflection_log_2286_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2287_neg : (40238537 / 500000000) ≤ -Real.log (250000 / 270951) ∧
    -Real.log (250000 / 270951) ≤ (3219083 / 40000000) := by
  have h := checkLog_sound (w := (20951 / 520951)) (n := 12)
    (lo := (40238537 / 500000000)) (hi := (3219083 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270951 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270951 / 250000) = 1/(250000 / 270951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2287 : Bounds (40238537 / 500000000) (3219083 / 40000000) (Real.log (270951 / 250000)) := by
  have h := reflection_log_2287_neg
  have he : Real.log (270951 / 250000) = -Real.log (250000 / 270951) := by
    rw [show ((270951 / 250000) : ℝ) = ((250000 / 270951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2288_neg : (87524963 / 1000000000) ≤ -Real.log (229049 / 250000) ∧
    -Real.log (229049 / 250000) ≤ (21881241 / 250000000) := by
  have h := checkLog_sound (w := (20951 / 479049)) (n := 12)
    (lo := (87524963 / 1000000000)) (hi := (21881241 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229049) = 1/(229049 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2288 : Bounds (-21881241 / 250000000) (-87524963 / 1000000000) (Real.log (229049 / 250000)) := by
  have h := reflection_log_2288_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2289_neg : (440493 / 62500000) ≤ -Real.log (62061055599 / 62500000000) ∧
    -Real.log (62061055599 / 62500000000) ≤ (7047889 / 1000000000) := by
  have h := checkLog_sound (w := (438944401 / 124561055599)) (n := 12)
    (lo := (440493 / 62500000)) (hi := (7047889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62061055599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62061055599) = 1/(62061055599 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2289 : Bounds (-7047889 / 1000000000) (-440493 / 62500000) (Real.log (62061055599 / 62500000000)) := by
  have h := reflection_log_2289_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2290_neg : (350557 / 50000000) ≤ -Real.log (248253345151 / 250000000000) ∧
    -Real.log (248253345151 / 250000000000) ≤ (7011141 / 1000000000) := by
  have h := checkLog_sound (w := (1746654849 / 498253345151)) (n := 12)
    (lo := (350557 / 50000000)) (hi := (7011141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248253345151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248253345151) = 1/(248253345151 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2290 : Bounds (-7011141 / 1000000000) (-350557 / 50000000) (Real.log (248253345151 / 250000000000)) := by
  have h := reflection_log_2290_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2291_neg : (83781481 / 500000000) ≤ -Real.log (500000000000 / 591209868029) ∧
    -Real.log (500000000000 / 591209868029) ≤ (167562963 / 1000000000) := by
  have h := checkLog_sound (w := (91209868029 / 1091209868029)) (n := 12)
    (lo := (83781481 / 500000000)) (hi := (167562963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591209868029 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591209868029 / 500000000000) = 1/(500000000000 / 591209868029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2291 : Bounds (83781481 / 500000000) (167562963 / 1000000000) (Real.log (591209868029 / 500000000000)) := by
  have h := reflection_log_2291_neg
  have he : Real.log (591209868029 / 500000000000) = -Real.log (500000000000 / 591209868029) := by
    rw [show ((591209868029 / 500000000000) : ℝ) = ((500000000000 / 591209868029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2292_neg : (84001019 / 500000000) ≤ -Real.log (500000000000 / 591469510891) ∧
    -Real.log (500000000000 / 591469510891) ≤ (168002039 / 1000000000) := by
  have h := checkLog_sound (w := (91469510891 / 1091469510891)) (n := 12)
    (lo := (84001019 / 500000000)) (hi := (168002039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591469510891 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591469510891 / 500000000000) = 1/(500000000000 / 591469510891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2292 : Bounds (84001019 / 500000000) (168002039 / 1000000000) (Real.log (591469510891 / 500000000000)) := by
  have h := reflection_log_2292_neg
  have he : Real.log (591469510891 / 500000000000) = -Real.log (500000000000 / 591469510891) := by
    rw [show ((591469510891 / 500000000000) : ℝ) = ((500000000000 / 591469510891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2293_neg : (336129389 / 1000000000) ≤ -Real.log (50000000000 / 69976004799) ∧
    -Real.log (50000000000 / 69976004799) ≤ (33612939 / 100000000) := by
  have h := checkLog_sound (w := (19976004799 / 119976004799)) (n := 12)
    (lo := (336129389 / 1000000000)) (hi := (33612939 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69976004799 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69976004799 / 50000000000) = 1/(50000000000 / 69976004799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2293 : Bounds (336129389 / 1000000000) (33612939 / 100000000) (Real.log (69976004799 / 50000000000)) := by
  have h := reflection_log_2293_neg
  have he : Real.log (69976004799 / 50000000000) = -Real.log (50000000000 / 69976004799) := by
    rw [show ((69976004799 / 50000000000) : ℝ) = ((50000000000 / 69976004799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2294_neg : (67267019 / 200000000) ≤ -Real.log (195312500 / 273400003) ∧
    -Real.log (195312500 / 273400003) ≤ (42041887 / 125000000) := by
  have h := checkLog_sound (w := (78087503 / 468712503)) (n := 12)
    (lo := (67267019 / 200000000)) (hi := (42041887 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273400003 / 195312500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273400003 / 195312500) = 1/(195312500 / 273400003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2294 : Bounds (67267019 / 200000000) (42041887 / 125000000) (Real.log (273400003 / 195312500)) := by
  have h := reflection_log_2294_neg
  have he : Real.log (273400003 / 195312500) = -Real.log (195312500 / 273400003) := by
    rw [show ((273400003 / 195312500) : ℝ) = ((195312500 / 273400003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2295_neg : (616717 / 4000000) ≤ -Real.log (10000 / 11667) ∧
    -Real.log (10000 / 11667) ≤ (154179251 / 1000000000) := by
  have h := checkLog_sound (w := (1667 / 21667)) (n := 12)
    (lo := (616717 / 4000000)) (hi := (154179251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11667 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11667 / 10000) = 1/(10000 / 11667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2295 : Bounds (616717 / 4000000) (154179251 / 1000000000) (Real.log (11667 / 10000)) := by
  have h := reflection_log_2295_neg
  have he : Real.log (11667 / 10000) = -Real.log (10000 / 11667) := by
    rw [show ((11667 / 10000) : ℝ) = ((10000 / 11667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2296_neg : (182361557 / 1000000000) ≤ -Real.log (8333 / 10000) ∧
    -Real.log (8333 / 10000) ≤ (91180779 / 500000000) := by
  have h := checkLog_sound (w := (1667 / 18333)) (n := 12)
    (lo := (182361557 / 1000000000)) (hi := (91180779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8333) = 1/(8333 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2296 : Bounds (-91180779 / 500000000) (-182361557 / 1000000000) (Real.log (8333 / 10000)) := by
  have h := reflection_log_2296_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2297_neg : (83343 / 500000000) ≤ -Real.log (10000000 / 10001667) ∧
    -Real.log (10000000 / 10001667) ≤ (166687 / 1000000000) := by
  have h := checkLog_sound (w := (1667 / 20001667)) (n := 12)
    (lo := (83343 / 500000000)) (hi := (166687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001667 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001667 / 10000000) = 1/(10000000 / 10001667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2297 : Bounds (83343 / 500000000) (166687 / 1000000000) (Real.log (10001667 / 10000000)) := by
  have h := reflection_log_2297_neg
  have he : Real.log (10001667 / 10000000) = -Real.log (10000000 / 10001667) := by
    rw [show ((10001667 / 10000000) : ℝ) = ((10000000 / 10001667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2298_neg : (166713 / 1000000000) ≤ -Real.log (9998333 / 10000000) ∧
    -Real.log (9998333 / 10000000) ≤ (83357 / 500000000) := by
  have h := checkLog_sound (w := (1667 / 19998333)) (n := 12)
    (lo := (166713 / 1000000000)) (hi := (83357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998333) = 1/(9998333 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2298 : Bounds (-83357 / 500000000) (-166713 / 1000000000) (Real.log (9998333 / 10000000)) := by
  have h := reflection_log_2298_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2299_neg : (2510093 / 31250000) ≤ -Real.log (1000000 / 1083637) ∧
    -Real.log (1000000 / 1083637) ≤ (80322977 / 1000000000) := by
  have h := checkLog_sound (w := (83637 / 2083637)) (n := 12)
    (lo := (2510093 / 31250000)) (hi := (80322977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083637 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083637 / 1000000) = 1/(1000000 / 1083637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2299 : Bounds (2510093 / 31250000) (80322977 / 1000000000) (Real.log (1083637 / 1000000)) := by
  have h := reflection_log_2299_neg
  have he : Real.log (1083637 / 1000000) = -Real.log (1000000 / 1083637) := by
    rw [show ((1083637 / 1000000) : ℝ) = ((1000000 / 1083637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2300_neg : (5458919 / 62500000) ≤ -Real.log (916363 / 1000000) ∧
    -Real.log (916363 / 1000000) ≤ (17468541 / 200000000) := by
  have h := checkLog_sound (w := (83637 / 1916363)) (n := 12)
    (lo := (5458919 / 62500000)) (hi := (17468541 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916363) = 1/(916363 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2300 : Bounds (-17468541 / 200000000) (-5458919 / 62500000) (Real.log (916363 / 1000000)) := by
  have h := reflection_log_2300_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2301_neg : (8052413 / 100000000) ≤ -Real.log (200000 / 216771) ∧
    -Real.log (200000 / 216771) ≤ (80524131 / 1000000000) := by
  have h := checkLog_sound (w := (16771 / 416771)) (n := 12)
    (lo := (8052413 / 100000000)) (hi := (80524131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216771 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216771 / 200000) = 1/(200000 / 216771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2301 : Bounds (8052413 / 100000000) (80524131 / 1000000000) (Real.log (216771 / 200000)) := by
  have h := reflection_log_2301_neg
  have he : Real.log (216771 / 200000) = -Real.log (200000 / 216771) := by
    rw [show ((216771 / 200000) : ℝ) = ((200000 / 216771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2302_neg : (87580629 / 1000000000) ≤ -Real.log (183229 / 200000) ∧
    -Real.log (183229 / 200000) ≤ (8758063 / 100000000) := by
  have h := checkLog_sound (w := (16771 / 383229)) (n := 12)
    (lo := (87580629 / 1000000000)) (hi := (8758063 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183229) = 1/(183229 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2302 : Bounds (-8758063 / 100000000) (-87580629 / 1000000000) (Real.log (183229 / 200000)) := by
  have h := reflection_log_2302_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2303_neg : (7056499 / 1000000000) ≤ -Real.log (39718733559 / 40000000000) ∧
    -Real.log (39718733559 / 40000000000) ≤ (14113 / 2000000) := by
  have h := checkLog_sound (w := (281266441 / 79718733559)) (n := 12)
    (lo := (7056499 / 1000000000)) (hi := (14113 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39718733559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39718733559) = 1/(39718733559 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2303 : Bounds (-14113 / 2000000) (-7056499 / 1000000000) (Real.log (39718733559 / 40000000000)) := by
  have h := reflection_log_2303_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
