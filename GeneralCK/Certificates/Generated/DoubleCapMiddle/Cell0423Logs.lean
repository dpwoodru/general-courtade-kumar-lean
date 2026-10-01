import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0423
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

theorem reflection_log_1_neg : (3893917 / 20000000) ≤ -Real.log (10240 / 12441) ∧
    -Real.log (10240 / 12441) ≤ (194695851 / 1000000000) := by
  have h := checkLog_sound (w := (2201 / 22681)) (n := 12)
    (lo := (3893917 / 20000000)) (hi := (194695851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12441 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12441 / 10240) = 1/(10240 / 12441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (3893917 / 20000000) (194695851 / 1000000000) (Real.log (12441 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12441 / 10240) = -Real.log (10240 / 12441) := by
    rw [show ((12441 / 10240) : ℝ) = ((10240 / 12441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (120998461 / 500000000) ≤ -Real.log (8039 / 10240) ∧
    -Real.log (8039 / 10240) ≤ (241996923 / 1000000000) := by
  have h := checkLog_sound (w := (2201 / 18279)) (n := 12)
    (lo := (120998461 / 500000000)) (hi := (241996923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8039) = 1/(8039 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-241996923 / 1000000000) (-120998461 / 500000000) (Real.log (8039 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (194454683 / 1000000000) ≤ -Real.log (5120 / 6219) ∧
    -Real.log (5120 / 6219) ≤ (48613671 / 250000000) := by
  have h := checkLog_sound (w := (1099 / 11339)) (n := 12)
    (lo := (194454683 / 1000000000)) (hi := (48613671 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6219 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6219 / 5120) = 1/(5120 / 6219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (194454683 / 1000000000) (48613671 / 250000000) (Real.log (6219 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6219 / 5120) = -Real.log (5120 / 6219) := by
    rw [show ((6219 / 5120) : ℝ) = ((5120 / 6219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (241623811 / 1000000000) ≤ -Real.log (4021 / 5120) ∧
    -Real.log (4021 / 5120) ≤ (60405953 / 250000000) := by
  have h := checkLog_sound (w := (1099 / 9141)) (n := 12)
    (lo := (241623811 / 1000000000)) (hi := (60405953 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 4021) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 4021) = 1/(4021 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-60405953 / 250000000) (-241623811 / 1000000000) (Real.log (4021 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (357592491 / 1000000000) ≤ -Real.log (5120 / 7321) ∧
    -Real.log (5120 / 7321) ≤ (89398123 / 250000000) := by
  have h := checkLog_sound (w := (2201 / 12441)) (n := 12)
    (lo := (357592491 / 1000000000)) (hi := (89398123 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7321 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7321 / 5120) = 1/(5120 / 7321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (357592491 / 1000000000) (89398123 / 250000000) (Real.log (7321 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7321 / 5120) = -Real.log (5120 / 7321) := by
    rw [show ((7321 / 5120) : ℝ) = ((5120 / 7321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (561913347 / 1000000000) ≤ -Real.log (2919 / 5120) ∧
    -Real.log (2919 / 5120) ≤ (140478337 / 250000000) := by
  have h := checkLog_sound (w := (2201 / 8039)) (n := 12)
    (lo := (561913347 / 1000000000)) (hi := (140478337 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2919) = 1/(2919 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-140478337 / 250000000) (-561913347 / 1000000000) (Real.log (2919 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (357182627 / 1000000000) ≤ -Real.log (2560 / 3659) ∧
    -Real.log (2560 / 3659) ≤ (89295657 / 250000000) := by
  have h := checkLog_sound (w := (1099 / 6219)) (n := 12)
    (lo := (357182627 / 1000000000)) (hi := (89295657 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3659 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3659 / 2560) = 1/(2560 / 3659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (357182627 / 1000000000) (89295657 / 250000000) (Real.log (3659 / 2560)) := by
  have h := reflection_log_7_neg
  have he : Real.log (3659 / 2560) = -Real.log (2560 / 3659) := by
    rw [show ((3659 / 2560) : ℝ) = ((2560 / 3659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (4487089 / 8000000) ≤ -Real.log (1461 / 2560) ∧
    -Real.log (1461 / 2560) ≤ (280443063 / 500000000) := by
  have h := checkLog_sound (w := (1099 / 4021)) (n := 12)
    (lo := (4487089 / 8000000)) (hi := (280443063 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1461) = 1/(1461 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-280443063 / 500000000) (-4487089 / 8000000) (Real.log (1461 / 2560)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (66758911 / 250000000) ≤ -Real.log (1000000 / 1306087) ∧
    -Real.log (1000000 / 1306087) ≤ (53407129 / 200000000) := by
  have h := checkLog_sound (w := (306087 / 2306087)) (n := 12)
    (lo := (66758911 / 250000000)) (hi := (53407129 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1306087 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1306087 / 1000000) = 1/(1000000 / 1306087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (66758911 / 250000000) (53407129 / 200000000) (Real.log (1306087 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1306087 / 1000000) = -Real.log (1000000 / 1306087) := by
    rw [show ((1306087 / 1000000) : ℝ) = ((1000000 / 1306087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (182704343 / 500000000) ≤ -Real.log (693913 / 1000000) ∧
    -Real.log (693913 / 1000000) ≤ (365408687 / 1000000000) := by
  have h := checkLog_sound (w := (306087 / 1693913)) (n := 12)
    (lo := (182704343 / 500000000)) (hi := (365408687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 693913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 693913) = 1/(693913 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-365408687 / 1000000000) (-182704343 / 500000000) (Real.log (693913 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (66840439 / 250000000) ≤ -Real.log (1000000 / 1306513) ∧
    -Real.log (1000000 / 1306513) ≤ (267361757 / 1000000000) := by
  have h := checkLog_sound (w := (306513 / 2306513)) (n := 12)
    (lo := (66840439 / 250000000)) (hi := (267361757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1306513 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1306513 / 1000000) = 1/(1000000 / 1306513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (66840439 / 250000000) (267361757 / 1000000000) (Real.log (1306513 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1306513 / 1000000) = -Real.log (1000000 / 1306513) := by
    rw [show ((1306513 / 1000000) : ℝ) = ((1000000 / 1306513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2859553 / 7812500) ≤ -Real.log (693487 / 1000000) ∧
    -Real.log (693487 / 1000000) ≤ (73204557 / 200000000) := by
  have h := checkLog_sound (w := (306513 / 1693487)) (n := 12)
    (lo := (2859553 / 7812500)) (hi := (73204557 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 693487) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 693487) = 1/(693487 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-73204557 / 200000000) (-2859553 / 7812500) (Real.log (693487 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (200652513 / 1000000000) ≤ -Real.log (5000 / 6111) ∧
    -Real.log (5000 / 6111) ≤ (100326257 / 500000000) := by
  have h := checkLog_sound (w := (1111 / 11111)) (n := 12)
    (lo := (200652513 / 1000000000)) (hi := (100326257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6111 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6111 / 5000) = 1/(5000 / 6111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (200652513 / 1000000000) (100326257 / 500000000) (Real.log (6111 / 5000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (6111 / 5000) = -Real.log (5000 / 6111) := by
    rw [show ((6111 / 5000) : ℝ) = ((5000 / 6111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (251285857 / 1000000000) ≤ -Real.log (3889 / 5000) ∧
    -Real.log (3889 / 5000) ≤ (125642929 / 500000000) := by
  have h := checkLog_sound (w := (1111 / 8889)) (n := 12)
    (lo := (251285857 / 1000000000)) (hi := (125642929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 3889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 3889) = 1/(3889 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-125642929 / 500000000) (-251285857 / 1000000000) (Real.log (3889 / 5000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (20091921 / 100000000) ≤ -Real.log (500000 / 611263) ∧
    -Real.log (500000 / 611263) ≤ (200919211 / 1000000000) := by
  have h := checkLog_sound (w := (111263 / 1111263)) (n := 12)
    (lo := (20091921 / 100000000)) (hi := (200919211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611263 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611263 / 500000) = 1/(500000 / 611263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (20091921 / 100000000) (200919211 / 1000000000) (Real.log (611263 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (611263 / 500000) = -Real.log (500000 / 611263) := by
    rw [show ((611263 / 500000) : ℝ) = ((500000 / 611263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (62926269 / 250000000) ≤ -Real.log (388737 / 500000) ∧
    -Real.log (388737 / 500000) ≤ (251705077 / 1000000000) := by
  have h := checkLog_sound (w := (111263 / 888737)) (n := 12)
    (lo := (62926269 / 250000000)) (hi := (251705077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 388737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 388737) = 1/(388737 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-251705077 / 1000000000) (-62926269 / 250000000) (Real.log (388737 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (63244433 / 100000000) ≤ -Real.log (250000000000 / 470551423593) ∧
    -Real.log (250000000000 / 470551423593) ≤ (632444331 / 1000000000) := by
  have h := checkLog_sound (w := (220551423593 / 720551423593)) (n := 12)
    (lo := (63244433 / 100000000)) (hi := (632444331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((470551423593 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(470551423593 / 250000000000) = 1/(250000000000 / 470551423593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (63244433 / 100000000) (632444331 / 1000000000) (Real.log (470551423593 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (470551423593 / 250000000000) = -Real.log (250000000000 / 470551423593) := by
    rw [show ((470551423593 / 250000000000) : ℝ) = ((250000000000 / 470551423593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (633384541 / 1000000000) ≤ -Real.log (500000000000 / 941988097831) ∧
    -Real.log (500000000000 / 941988097831) ≤ (316692271 / 500000000) := by
  have h := checkLog_sound (w := (441988097831 / 1441988097831)) (n := 12)
    (lo := (633384541 / 1000000000)) (hi := (316692271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((941988097831 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(941988097831 / 500000000000) = 1/(500000000000 / 941988097831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (633384541 / 1000000000) (316692271 / 500000000) (Real.log (941988097831 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (941988097831 / 500000000000) = -Real.log (500000000000 / 941988097831) := by
    rw [show ((941988097831 / 500000000000) : ℝ) = ((500000000000 / 941988097831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (45193837 / 100000000) ≤ -Real.log (500000000000 / 785677552069) ∧
    -Real.log (500000000000 / 785677552069) ≤ (451938371 / 1000000000) := by
  have h := checkLog_sound (w := (285677552069 / 1285677552069)) (n := 12)
    (lo := (45193837 / 100000000)) (hi := (451938371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((785677552069 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(785677552069 / 500000000000) = 1/(500000000000 / 785677552069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (45193837 / 100000000) (451938371 / 1000000000) (Real.log (785677552069 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (785677552069 / 500000000000) = -Real.log (500000000000 / 785677552069) := by
    rw [show ((785677552069 / 500000000000) : ℝ) = ((500000000000 / 785677552069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (226312143 / 500000000) ≤ -Real.log (500000000000 / 786216645187) ∧
    -Real.log (500000000000 / 786216645187) ≤ (452624287 / 1000000000) := by
  have h := checkLog_sound (w := (286216645187 / 1286216645187)) (n := 12)
    (lo := (226312143 / 500000000)) (hi := (452624287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((786216645187 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(786216645187 / 500000000000) = 1/(500000000000 / 786216645187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (226312143 / 500000000) (452624287 / 1000000000) (Real.log (786216645187 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (786216645187 / 500000000000) = -Real.log (500000000000 / 786216645187) := by
    rw [show ((786216645187 / 500000000000) : ℝ) = ((500000000000 / 786216645187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0423
