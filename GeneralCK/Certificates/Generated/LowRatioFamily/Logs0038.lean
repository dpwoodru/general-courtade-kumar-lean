import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2432_neg : (42256317 / 250000000) ≤ -Real.log (500000000000 / 592075029923) ∧
    -Real.log (500000000000 / 592075029923) ≤ (169025269 / 1000000000) := by
  have h := checkLog_sound (w := (92075029923 / 1092075029923)) (n := 12)
    (lo := (42256317 / 250000000)) (hi := (169025269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592075029923 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592075029923 / 500000000000) = 1/(500000000000 / 592075029923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2432 : Bounds (42256317 / 250000000) (169025269 / 1000000000) (Real.log (592075029923 / 500000000000)) := by
  have h := reflection_log_2432_neg
  have he : Real.log (592075029923 / 500000000000) = -Real.log (500000000000 / 592075029923) := by
    rw [show ((592075029923 / 500000000000) : ℝ) = ((500000000000 / 592075029923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2433_neg : (338186767 / 1000000000) ≤ -Real.log (500000000000 / 701201201201) ∧
    -Real.log (500000000000 / 701201201201) ≤ (21136673 / 62500000) := by
  have h := checkLog_sound (w := (201201201201 / 1201201201201)) (n := 12)
    (lo := (338186767 / 1000000000)) (hi := (21136673 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((701201201201 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(701201201201 / 500000000000) = 1/(500000000000 / 701201201201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2433 : Bounds (338186767 / 1000000000) (21136673 / 62500000) (Real.log (701201201201 / 500000000000)) := by
  have h := reflection_log_2433_neg
  have he : Real.log (701201201201 / 500000000000) = -Real.log (500000000000 / 701201201201) := by
    rw [show ((701201201201 / 500000000000) : ℝ) = ((500000000000 / 701201201201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2434_neg : (10574767 / 31250000) ≤ -Real.log (62500000000 / 87668188371) ∧
    -Real.log (62500000000 / 87668188371) ≤ (67678509 / 200000000) := by
  have h := checkLog_sound (w := (25168188371 / 150168188371)) (n := 12)
    (lo := (10574767 / 31250000)) (hi := (67678509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87668188371 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87668188371 / 62500000000) = 1/(62500000000 / 87668188371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2434 : Bounds (10574767 / 31250000) (67678509 / 200000000) (Real.log (87668188371 / 62500000000)) := by
  have h := reflection_log_2434_neg
  have he : Real.log (87668188371 / 62500000000) = -Real.log (62500000000 / 87668188371) := by
    rw [show ((87668188371 / 62500000000) : ℝ) = ((62500000000 / 87668188371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2435_neg : (77518001 / 500000000) ≤ -Real.log (10000 / 11677) ∧
    -Real.log (10000 / 11677) ≤ (155036003 / 1000000000) := by
  have h := checkLog_sound (w := (1677 / 21677)) (n := 12)
    (lo := (77518001 / 500000000)) (hi := (155036003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11677 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11677 / 10000) = 1/(10000 / 11677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2435 : Bounds (77518001 / 500000000) (155036003 / 1000000000) (Real.log (11677 / 10000)) := by
  have h := reflection_log_2435_neg
  have he : Real.log (11677 / 10000) = -Real.log (10000 / 11677) := by
    rw [show ((11677 / 10000) : ℝ) = ((10000 / 11677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2436_neg : (91781163 / 500000000) ≤ -Real.log (8323 / 10000) ∧
    -Real.log (8323 / 10000) ≤ (183562327 / 1000000000) := by
  have h := checkLog_sound (w := (1677 / 18323)) (n := 12)
    (lo := (91781163 / 500000000)) (hi := (183562327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8323) = 1/(8323 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2436 : Bounds (-183562327 / 1000000000) (-91781163 / 500000000) (Real.log (8323 / 10000)) := by
  have h := reflection_log_2436_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2437_neg : (33537 / 200000000) ≤ -Real.log (10000000 / 10001677) ∧
    -Real.log (10000000 / 10001677) ≤ (83843 / 500000000) := by
  have h := checkLog_sound (w := (1677 / 20001677)) (n := 12)
    (lo := (33537 / 200000000)) (hi := (83843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001677 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001677 / 10000000) = 1/(10000000 / 10001677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2437 : Bounds (33537 / 200000000) (83843 / 500000000) (Real.log (10001677 / 10000000)) := by
  have h := reflection_log_2437_neg
  have he : Real.log (10001677 / 10000000) = -Real.log (10000000 / 10001677) := by
    rw [show ((10001677 / 10000000) : ℝ) = ((10000000 / 10001677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2438_neg : (83857 / 500000000) ≤ -Real.log (9998323 / 10000000) ∧
    -Real.log (9998323 / 10000000) ≤ (33543 / 200000000) := by
  have h := checkLog_sound (w := (1677 / 19998323)) (n := 12)
    (lo := (83857 / 500000000)) (hi := (33543 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998323) = 1/(9998323 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2438 : Bounds (-33543 / 200000000) (-83857 / 500000000) (Real.log (9998323 / 10000000)) := by
  have h := reflection_log_2438_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2439_neg : (16158147 / 200000000) ≤ -Real.log (62500 / 67759) ∧
    -Real.log (62500 / 67759) ≤ (5049421 / 62500000) := by
  have h := checkLog_sound (w := (5259 / 130259)) (n := 12)
    (lo := (16158147 / 200000000)) (hi := (5049421 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67759 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67759 / 62500) = 1/(62500 / 67759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2439 : Bounds (16158147 / 200000000) (5049421 / 62500000) (Real.log (67759 / 62500)) := by
  have h := reflection_log_2439_neg
  have he : Real.log (67759 / 62500) = -Real.log (62500 / 67759) := by
    rw [show ((67759 / 62500) : ℝ) = ((62500 / 67759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2440_neg : (87896131 / 1000000000) ≤ -Real.log (57241 / 62500) ∧
    -Real.log (57241 / 62500) ≤ (21974033 / 250000000) := by
  have h := checkLog_sound (w := (5259 / 119741)) (n := 12)
    (lo := (87896131 / 1000000000)) (hi := (21974033 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 57241) = 1/(57241 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2440 : Bounds (-21974033 / 250000000) (-87896131 / 1000000000) (Real.log (57241 / 62500)) := by
  have h := reflection_log_2440_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2441_neg : (80992717 / 1000000000) ≤ -Real.log (1000000 / 1084363) ∧
    -Real.log (1000000 / 1084363) ≤ (40496359 / 500000000) := by
  have h := checkLog_sound (w := (84363 / 2084363)) (n := 12)
    (lo := (80992717 / 1000000000)) (hi := (40496359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084363 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084363 / 1000000) = 1/(1000000 / 1084363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2441 : Bounds (80992717 / 1000000000) (40496359 / 500000000) (Real.log (1084363 / 1000000)) := by
  have h := reflection_log_2441_neg
  have he : Real.log (1084363 / 1000000) = -Real.log (1000000 / 1084363) := by
    rw [show ((1084363 / 1000000) : ℝ) = ((1000000 / 1084363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2442_neg : (88135281 / 1000000000) ≤ -Real.log (915637 / 1000000) ∧
    -Real.log (915637 / 1000000) ≤ (44067641 / 500000000) := by
  have h := checkLog_sound (w := (84363 / 1915637)) (n := 12)
    (lo := (88135281 / 1000000000)) (hi := (44067641 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915637) = 1/(915637 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2442 : Bounds (-44067641 / 500000000) (-88135281 / 1000000000) (Real.log (915637 / 1000000)) := by
  have h := reflection_log_2442_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2443_neg : (7142563 / 1000000000) ≤ -Real.log (992882884231 / 1000000000000) ∧
    -Real.log (992882884231 / 1000000000000) ≤ (1785641 / 250000000) := by
  have h := checkLog_sound (w := (7117115769 / 1992882884231)) (n := 12)
    (lo := (7142563 / 1000000000)) (hi := (1785641 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992882884231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992882884231) = 1/(992882884231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2443 : Bounds (-1785641 / 250000000) (-7142563 / 1000000000) (Real.log (992882884231 / 1000000000000)) := by
  have h := reflection_log_2443_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2444_neg : (1776349 / 250000000) ≤ -Real.log (3878592919 / 3906250000) ∧
    -Real.log (3878592919 / 3906250000) ≤ (7105397 / 1000000000) := by
  have h := checkLog_sound (w := (27657081 / 7784842919)) (n := 12)
    (lo := (1776349 / 250000000)) (hi := (7105397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3878592919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3878592919) = 1/(3878592919 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2444 : Bounds (-7105397 / 1000000000) (-1776349 / 250000000) (Real.log (3878592919 / 3906250000)) := by
  have h := reflection_log_2444_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2445_neg : (168686867 / 1000000000) ≤ -Real.log (500000000000 / 591874705193) ∧
    -Real.log (500000000000 / 591874705193) ≤ (42171717 / 250000000) := by
  have h := checkLog_sound (w := (91874705193 / 1091874705193)) (n := 12)
    (lo := (168686867 / 1000000000)) (hi := (42171717 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591874705193 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591874705193 / 500000000000) = 1/(500000000000 / 591874705193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2445 : Bounds (168686867 / 1000000000) (42171717 / 250000000) (Real.log (591874705193 / 500000000000)) := by
  have h := reflection_log_2445_neg
  have he : Real.log (591874705193 / 500000000000) = -Real.log (500000000000 / 591874705193) := by
    rw [show ((591874705193 / 500000000000) : ℝ) = ((500000000000 / 591874705193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2446_neg : (84563999 / 500000000) ≤ -Real.log (500000000000 / 592135857333) ∧
    -Real.log (500000000000 / 592135857333) ≤ (169127999 / 1000000000) := by
  have h := checkLog_sound (w := (92135857333 / 1092135857333)) (n := 12)
    (lo := (84563999 / 500000000)) (hi := (169127999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592135857333 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592135857333 / 500000000000) = 1/(500000000000 / 592135857333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2446 : Bounds (84563999 / 500000000) (169127999 / 1000000000) (Real.log (592135857333 / 500000000000)) := by
  have h := reflection_log_2446_neg
  have he : Real.log (592135857333 / 500000000000) = -Real.log (500000000000 / 592135857333) := by
    rw [show ((592135857333 / 500000000000) : ℝ) = ((500000000000 / 592135857333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2447_neg : (10574767 / 31250000) ≤ -Real.log (500000000000 / 701345506967) ∧
    -Real.log (500000000000 / 701345506967) ≤ (67678509 / 200000000) := by
  have h := checkLog_sound (w := (201345506967 / 1201345506967)) (n := 12)
    (lo := (10574767 / 31250000)) (hi := (67678509 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((701345506967 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(701345506967 / 500000000000) = 1/(500000000000 / 701345506967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2447 : Bounds (10574767 / 31250000) (67678509 / 200000000) (Real.log (701345506967 / 500000000000)) := by
  have h := reflection_log_2447_neg
  have he : Real.log (701345506967 / 500000000000) = -Real.log (500000000000 / 701345506967) := by
    rw [show ((701345506967 / 500000000000) : ℝ) = ((500000000000 / 701345506967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2448_neg : (42324791 / 125000000) ≤ -Real.log (500000000000 / 701489847411) ∧
    -Real.log (500000000000 / 701489847411) ≤ (338598329 / 1000000000) := by
  have h := checkLog_sound (w := (201489847411 / 1201489847411)) (n := 12)
    (lo := (42324791 / 125000000)) (hi := (338598329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((701489847411 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(701489847411 / 500000000000) = 1/(500000000000 / 701489847411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2448 : Bounds (42324791 / 125000000) (338598329 / 1000000000) (Real.log (701489847411 / 500000000000)) := by
  have h := reflection_log_2448_neg
  have he : Real.log (701489847411 / 500000000000) = -Real.log (500000000000 / 701489847411) := by
    rw [show ((701489847411 / 500000000000) : ℝ) = ((500000000000 / 701489847411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2449_neg : (38780409 / 250000000) ≤ -Real.log (5000 / 5839) ∧
    -Real.log (5000 / 5839) ≤ (155121637 / 1000000000) := by
  have h := checkLog_sound (w := (839 / 10839)) (n := 12)
    (lo := (38780409 / 250000000)) (hi := (155121637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5839 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5839 / 5000) = 1/(5000 / 5839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2449 : Bounds (38780409 / 250000000) (155121637 / 1000000000) (Real.log (5839 / 5000)) := by
  have h := reflection_log_2449_neg
  have he : Real.log (5839 / 5000) = -Real.log (5000 / 5839) := by
    rw [show ((5839 / 5000) : ℝ) = ((5000 / 5839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2450_neg : (91841241 / 500000000) ≤ -Real.log (4161 / 5000) ∧
    -Real.log (4161 / 5000) ≤ (183682483 / 1000000000) := by
  have h := checkLog_sound (w := (839 / 9161)) (n := 12)
    (lo := (91841241 / 500000000)) (hi := (183682483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4161) = 1/(4161 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2450 : Bounds (-183682483 / 1000000000) (-91841241 / 500000000) (Real.log (4161 / 5000)) := by
  have h := reflection_log_2450_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2451_neg : (33557 / 200000000) ≤ -Real.log (5000000 / 5000839) ∧
    -Real.log (5000000 / 5000839) ≤ (83893 / 500000000) := by
  have h := checkLog_sound (w := (839 / 10000839)) (n := 12)
    (lo := (33557 / 200000000)) (hi := (83893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000839 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000839 / 5000000) = 1/(5000000 / 5000839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2451 : Bounds (33557 / 200000000) (83893 / 500000000) (Real.log (5000839 / 5000000)) := by
  have h := reflection_log_2451_neg
  have he : Real.log (5000839 / 5000000) = -Real.log (5000000 / 5000839) := by
    rw [show ((5000839 / 5000000) : ℝ) = ((5000000 / 5000839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2452_neg : (83907 / 500000000) ≤ -Real.log (4999161 / 5000000) ∧
    -Real.log (4999161 / 5000000) ≤ (33563 / 200000000) := by
  have h := checkLog_sound (w := (839 / 9999161)) (n := 12)
    (lo := (83907 / 500000000)) (hi := (33563 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999161) = 1/(4999161 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2452 : Bounds (-33563 / 200000000) (-83907 / 500000000) (Real.log (4999161 / 5000000)) := by
  have h := reflection_log_2452_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2453_neg : (5052361 / 62500000) ≤ -Real.log (200000 / 216839) ∧
    -Real.log (200000 / 216839) ≤ (80837777 / 1000000000) := by
  have h := checkLog_sound (w := (16839 / 416839)) (n := 12)
    (lo := (5052361 / 62500000)) (hi := (80837777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216839 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216839 / 200000) = 1/(200000 / 216839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2453 : Bounds (5052361 / 62500000) (80837777 / 1000000000) (Real.log (216839 / 200000)) := by
  have h := reflection_log_2453_neg
  have he : Real.log (216839 / 200000) = -Real.log (200000 / 216839) := by
    rw [show ((216839 / 200000) : ℝ) = ((200000 / 216839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2454_neg : (87951819 / 1000000000) ≤ -Real.log (183161 / 200000) ∧
    -Real.log (183161 / 200000) ≤ (4397591 / 50000000) := by
  have h := checkLog_sound (w := (16839 / 383161)) (n := 12)
    (lo := (87951819 / 1000000000)) (hi := (4397591 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183161) = 1/(183161 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2454 : Bounds (-4397591 / 50000000) (-87951819 / 1000000000) (Real.log (183161 / 200000)) := by
  have h := reflection_log_2454_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2455_neg : (20259937 / 250000000) ≤ -Real.log (500000 / 542207) ∧
    -Real.log (500000 / 542207) ≤ (81039749 / 1000000000) := by
  have h := checkLog_sound (w := (42207 / 1042207)) (n := 12)
    (lo := (20259937 / 250000000)) (hi := (81039749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542207 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542207 / 500000) = 1/(500000 / 542207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2455 : Bounds (20259937 / 250000000) (81039749 / 1000000000) (Real.log (542207 / 500000)) := by
  have h := reflection_log_2455_neg
  have he : Real.log (542207 / 500000) = -Real.log (500000 / 542207) := by
    rw [show ((542207 / 500000) : ℝ) = ((500000 / 542207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2456_neg : (88190981 / 1000000000) ≤ -Real.log (457793 / 500000) ∧
    -Real.log (457793 / 500000) ≤ (44095491 / 500000000) := by
  have h := checkLog_sound (w := (42207 / 957793)) (n := 12)
    (lo := (88190981 / 1000000000)) (hi := (44095491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457793) = 1/(457793 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2456 : Bounds (-44095491 / 500000000) (-88190981 / 1000000000) (Real.log (457793 / 500000)) := by
  have h := reflection_log_2456_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2457_neg : (55869 / 7812500) ≤ -Real.log (248218569151 / 250000000000) ∧
    -Real.log (248218569151 / 250000000000) ≤ (7151233 / 1000000000) := by
  have h := checkLog_sound (w := (1781430849 / 498218569151)) (n := 12)
    (lo := (55869 / 7812500)) (hi := (7151233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248218569151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248218569151) = 1/(248218569151 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2457 : Bounds (-7151233 / 1000000000) (-55869 / 7812500) (Real.log (248218569151 / 250000000000)) := by
  have h := reflection_log_2457_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2458_neg : (3557021 / 500000000) ≤ -Real.log (39716448079 / 40000000000) ∧
    -Real.log (39716448079 / 40000000000) ≤ (7114043 / 1000000000) := by
  have h := checkLog_sound (w := (283551921 / 79716448079)) (n := 12)
    (lo := (3557021 / 500000000)) (hi := (7114043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39716448079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39716448079) = 1/(39716448079 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2458 : Bounds (-7114043 / 1000000000) (-3557021 / 500000000) (Real.log (39716448079 / 40000000000)) := by
  have h := reflection_log_2458_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2459_neg : (33757919 / 200000000) ≤ -Real.log (31250000000 / 36995969393) ∧
    -Real.log (31250000000 / 36995969393) ≤ (42197399 / 250000000) := by
  have h := checkLog_sound (w := (5745969393 / 68245969393)) (n := 12)
    (lo := (33757919 / 200000000)) (hi := (42197399 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36995969393 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36995969393 / 31250000000) = 1/(31250000000 / 36995969393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2459 : Bounds (33757919 / 200000000) (42197399 / 250000000) (Real.log (36995969393 / 31250000000)) := by
  have h := reflection_log_2459_neg
  have he : Real.log (36995969393 / 31250000000) = -Real.log (31250000000 / 36995969393) := by
    rw [show ((36995969393 / 31250000000) : ℝ) = ((31250000000 / 36995969393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2460_neg : (16923073 / 100000000) ≤ -Real.log (250000000000 / 296098345759) ∧
    -Real.log (250000000000 / 296098345759) ≤ (169230731 / 1000000000) := by
  have h := checkLog_sound (w := (46098345759 / 546098345759)) (n := 12)
    (lo := (16923073 / 100000000)) (hi := (169230731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296098345759 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296098345759 / 250000000000) = 1/(250000000000 / 296098345759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2460 : Bounds (16923073 / 100000000) (169230731 / 1000000000) (Real.log (296098345759 / 250000000000)) := by
  have h := reflection_log_2460_neg
  have he : Real.log (296098345759 / 250000000000) = -Real.log (250000000000 / 296098345759) := by
    rw [show ((296098345759 / 250000000000) : ℝ) = ((250000000000 / 296098345759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2461_neg : (42324791 / 125000000) ≤ -Real.log (50000000000 / 70148984741) ∧
    -Real.log (50000000000 / 70148984741) ≤ (338598329 / 1000000000) := by
  have h := checkLog_sound (w := (20148984741 / 120148984741)) (n := 12)
    (lo := (42324791 / 125000000)) (hi := (338598329 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70148984741 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(70148984741 / 50000000000) = 1/(50000000000 / 70148984741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2461 : Bounds (42324791 / 125000000) (338598329 / 1000000000) (Real.log (70148984741 / 50000000000)) := by
  have h := reflection_log_2461_neg
  have he : Real.log (70148984741 / 50000000000) = -Real.log (50000000000 / 70148984741) := by
    rw [show ((70148984741 / 50000000000) : ℝ) = ((50000000000 / 70148984741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2462_neg : (338804119 / 1000000000) ≤ -Real.log (500000000000 / 701634222543) ∧
    -Real.log (500000000000 / 701634222543) ≤ (8470103 / 25000000) := by
  have h := checkLog_sound (w := (201634222543 / 1201634222543)) (n := 12)
    (lo := (338804119 / 1000000000)) (hi := (8470103 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((701634222543 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(701634222543 / 500000000000) = 1/(500000000000 / 701634222543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2462 : Bounds (338804119 / 1000000000) (8470103 / 25000000) (Real.log (701634222543 / 500000000000)) := by
  have h := reflection_log_2462_neg
  have he : Real.log (701634222543 / 500000000000) = -Real.log (500000000000 / 701634222543) := by
    rw [show ((701634222543 / 500000000000) : ℝ) = ((500000000000 / 701634222543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2463_neg : (4850227 / 31250000) ≤ -Real.log (10000 / 11679) ∧
    -Real.log (10000 / 11679) ≤ (31041453 / 200000000) := by
  have h := checkLog_sound (w := (1679 / 21679)) (n := 12)
    (lo := (4850227 / 31250000)) (hi := (31041453 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11679 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11679 / 10000) = 1/(10000 / 11679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2463 : Bounds (4850227 / 31250000) (31041453 / 200000000) (Real.log (11679 / 10000)) := by
  have h := reflection_log_2463_neg
  have he : Real.log (11679 / 10000) = -Real.log (10000 / 11679) := by
    rw [show ((11679 / 10000) : ℝ) = ((10000 / 11679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2464_neg : (183802653 / 1000000000) ≤ -Real.log (8321 / 10000) ∧
    -Real.log (8321 / 10000) ≤ (91901327 / 500000000) := by
  have h := checkLog_sound (w := (1679 / 18321)) (n := 12)
    (lo := (183802653 / 1000000000)) (hi := (91901327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8321) = 1/(8321 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2464 : Bounds (-91901327 / 500000000) (-183802653 / 1000000000) (Real.log (8321 / 10000)) := by
  have h := reflection_log_2464_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2465_neg : (33577 / 200000000) ≤ -Real.log (10000000 / 10001679) ∧
    -Real.log (10000000 / 10001679) ≤ (83943 / 500000000) := by
  have h := checkLog_sound (w := (1679 / 20001679)) (n := 12)
    (lo := (33577 / 200000000)) (hi := (83943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001679 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001679 / 10000000) = 1/(10000000 / 10001679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2465 : Bounds (33577 / 200000000) (83943 / 500000000) (Real.log (10001679 / 10000000)) := by
  have h := reflection_log_2465_neg
  have he : Real.log (10001679 / 10000000) = -Real.log (10000000 / 10001679) := by
    rw [show ((10001679 / 10000000) : ℝ) = ((10000000 / 10001679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2466_neg : (83957 / 500000000) ≤ -Real.log (9998321 / 10000000) ∧
    -Real.log (9998321 / 10000000) ≤ (33583 / 200000000) := by
  have h := checkLog_sound (w := (1679 / 19998321)) (n := 12)
    (lo := (83957 / 500000000)) (hi := (33583 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998321) = 1/(9998321 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2466 : Bounds (-33583 / 200000000) (-83957 / 500000000) (Real.log (9998321 / 10000000)) := by
  have h := reflection_log_2466_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2467_neg : (40442407 / 500000000) ≤ -Real.log (500000 / 542123) ∧
    -Real.log (500000 / 542123) ≤ (16176963 / 200000000) := by
  have h := checkLog_sound (w := (42123 / 1042123)) (n := 12)
    (lo := (40442407 / 500000000)) (hi := (16176963 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542123 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542123 / 500000) = 1/(500000 / 542123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2467 : Bounds (40442407 / 500000000) (16176963 / 200000000) (Real.log (542123 / 500000)) := by
  have h := reflection_log_2467_neg
  have he : Real.log (542123 / 500000) = -Real.log (500000 / 542123) := by
    rw [show ((542123 / 500000) : ℝ) = ((500000 / 542123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2468_neg : (88007509 / 1000000000) ≤ -Real.log (457877 / 500000) ∧
    -Real.log (457877 / 500000) ≤ (8800751 / 100000000) := by
  have h := checkLog_sound (w := (42123 / 957877)) (n := 12)
    (lo := (88007509 / 1000000000)) (hi := (8800751 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457877) = 1/(457877 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2468 : Bounds (-8800751 / 100000000) (-88007509 / 1000000000) (Real.log (457877 / 500000)) := by
  have h := reflection_log_2468_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2469_neg : (16217171 / 200000000) ≤ -Real.log (62500 / 67779) ∧
    -Real.log (62500 / 67779) ≤ (2533933 / 31250000) := by
  have h := checkLog_sound (w := (5279 / 130279)) (n := 12)
    (lo := (16217171 / 200000000)) (hi := (2533933 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67779 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67779 / 62500) = 1/(62500 / 67779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2469 : Bounds (16217171 / 200000000) (2533933 / 31250000) (Real.log (67779 / 62500)) := by
  have h := reflection_log_2469_neg
  have he : Real.log (67779 / 62500) = -Real.log (62500 / 67779) := by
    rw [show ((67779 / 62500) : ℝ) = ((62500 / 67779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2470_neg : (11030699 / 125000000) ≤ -Real.log (57221 / 62500) ∧
    -Real.log (57221 / 62500) ≤ (88245593 / 1000000000) := by
  have h := checkLog_sound (w := (5279 / 119721)) (n := 12)
    (lo := (11030699 / 125000000)) (hi := (88245593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 57221) = 1/(57221 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2470 : Bounds (-88245593 / 1000000000) (-11030699 / 125000000) (Real.log (57221 / 62500)) := by
  have h := reflection_log_2470_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2471_neg : (7159737 / 1000000000) ≤ -Real.log (3878382159 / 3906250000) ∧
    -Real.log (3878382159 / 3906250000) ≤ (3579869 / 500000000) := by
  have h := checkLog_sound (w := (27867841 / 7784632159)) (n := 12)
    (lo := (7159737 / 1000000000)) (hi := (3579869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3878382159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3878382159) = 1/(3878382159 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2471 : Bounds (-3579869 / 500000000) (-7159737 / 1000000000) (Real.log (3878382159 / 3906250000)) := by
  have h := reflection_log_2471_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2472_neg : (3561347 / 500000000) ≤ -Real.log (248225652871 / 250000000000) ∧
    -Real.log (248225652871 / 250000000000) ≤ (1424539 / 200000000) := by
  have h := checkLog_sound (w := (1774347129 / 498225652871)) (n := 12)
    (lo := (3561347 / 500000000)) (hi := (1424539 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248225652871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248225652871) = 1/(248225652871 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2472 : Bounds (-1424539 / 200000000) (-3561347 / 500000000) (Real.log (248225652871 / 250000000000)) := by
  have h := reflection_log_2472_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2473_neg : (168892323 / 1000000000) ≤ -Real.log (125000000000 / 147999080539) ∧
    -Real.log (125000000000 / 147999080539) ≤ (42223081 / 250000000) := by
  have h := checkLog_sound (w := (22999080539 / 272999080539)) (n := 12)
    (lo := (168892323 / 1000000000)) (hi := (42223081 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147999080539 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147999080539 / 125000000000) = 1/(125000000000 / 147999080539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2473 : Bounds (168892323 / 1000000000) (42223081 / 250000000) (Real.log (147999080539 / 125000000000)) := by
  have h := reflection_log_2473_neg
  have he : Real.log (147999080539 / 125000000000) = -Real.log (125000000000 / 147999080539) := by
    rw [show ((147999080539 / 125000000000) : ℝ) = ((125000000000 / 147999080539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2474_neg : (21166431 / 125000000) ≤ -Real.log (976562500 / 1156750663) ∧
    -Real.log (976562500 / 1156750663) ≤ (169331449 / 1000000000) := by
  have h := checkLog_sound (w := (180188163 / 2133313163)) (n := 12)
    (lo := (21166431 / 125000000)) (hi := (169331449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1156750663 / 976562500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1156750663 / 976562500) = 1/(976562500 / 1156750663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2474 : Bounds (21166431 / 125000000) (169331449 / 1000000000) (Real.log (1156750663 / 976562500)) := by
  have h := reflection_log_2474_neg
  have he : Real.log (1156750663 / 976562500) = -Real.log (976562500 / 1156750663) := by
    rw [show ((1156750663 / 976562500) : ℝ) = ((976562500 / 1156750663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2475_neg : (338804119 / 1000000000) ≤ -Real.log (250000000000 / 350817111271) ∧
    -Real.log (250000000000 / 350817111271) ≤ (8470103 / 25000000) := by
  have h := checkLog_sound (w := (100817111271 / 600817111271)) (n := 12)
    (lo := (338804119 / 1000000000)) (hi := (8470103 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((350817111271 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(350817111271 / 250000000000) = 1/(250000000000 / 350817111271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2475 : Bounds (338804119 / 1000000000) (8470103 / 25000000) (Real.log (350817111271 / 250000000000)) := by
  have h := reflection_log_2475_neg
  have he : Real.log (350817111271 / 250000000000) = -Real.log (250000000000 / 350817111271) := by
    rw [show ((350817111271 / 250000000000) : ℝ) = ((250000000000 / 350817111271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2476_neg : (339009917 / 1000000000) ≤ -Real.log (62500000000 / 87722329047) ∧
    -Real.log (62500000000 / 87722329047) ≤ (169504959 / 500000000) := by
  have h := checkLog_sound (w := (25222329047 / 150222329047)) (n := 12)
    (lo := (339009917 / 1000000000)) (hi := (169504959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87722329047 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87722329047 / 62500000000) = 1/(62500000000 / 87722329047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2476 : Bounds (339009917 / 1000000000) (169504959 / 500000000) (Real.log (87722329047 / 62500000000)) := by
  have h := reflection_log_2476_neg
  have he : Real.log (87722329047 / 62500000000) = -Real.log (62500000000 / 87722329047) := by
    rw [show ((87722329047 / 62500000000) : ℝ) = ((62500000000 / 87722329047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2477_neg : (38823221 / 250000000) ≤ -Real.log (125 / 146) ∧
    -Real.log (125 / 146) ≤ (31058577 / 200000000) := by
  have h := checkLog_sound (w := (21 / 271)) (n := 12)
    (lo := (38823221 / 250000000)) (hi := (31058577 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146 / 125) = 1/(125 / 146) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2477 : Bounds (38823221 / 250000000) (31058577 / 200000000) (Real.log (146 / 125)) := by
  have h := reflection_log_2477_neg
  have he : Real.log (146 / 125) = -Real.log (125 / 146) := by
    rw [show ((146 / 125) : ℝ) = ((125 / 146) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2478_neg : (91961419 / 500000000) ≤ -Real.log (104 / 125) ∧
    -Real.log (104 / 125) ≤ (183922839 / 1000000000) := by
  have h := checkLog_sound (w := (21 / 229)) (n := 12)
    (lo := (91961419 / 500000000)) (hi := (183922839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 104) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 104) = 1/(104 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2478 : Bounds (-183922839 / 1000000000) (-91961419 / 500000000) (Real.log (104 / 125)) := by
  have h := reflection_log_2478_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2479_neg : (33597 / 200000000) ≤ -Real.log (125000 / 125021) ∧
    -Real.log (125000 / 125021) ≤ (83993 / 500000000) := by
  have h := checkLog_sound (w := (21 / 250021)) (n := 12)
    (lo := (33597 / 200000000)) (hi := (83993 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125021 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125021 / 125000) = 1/(125000 / 125021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2479 : Bounds (33597 / 200000000) (83993 / 500000000) (Real.log (125021 / 125000)) := by
  have h := reflection_log_2479_neg
  have he : Real.log (125021 / 125000) = -Real.log (125000 / 125021) := by
    rw [show ((125021 / 125000) : ℝ) = ((125000 / 125021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2480_neg : (84007 / 500000000) ≤ -Real.log (124979 / 125000) ∧
    -Real.log (124979 / 125000) ≤ (33603 / 200000000) := by
  have h := checkLog_sound (w := (21 / 249979)) (n := 12)
    (lo := (84007 / 500000000)) (hi := (33603 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124979) = 1/(124979 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2480 : Bounds (-33603 / 200000000) (-84007 / 500000000) (Real.log (124979 / 125000)) := by
  have h := reflection_log_2480_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2481_neg : (5058183 / 62500000) ≤ -Real.log (125000 / 135537) ∧
    -Real.log (125000 / 135537) ≤ (80930929 / 1000000000) := by
  have h := checkLog_sound (w := (10537 / 260537)) (n := 12)
    (lo := (5058183 / 62500000)) (hi := (80930929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135537 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135537 / 125000) = 1/(125000 / 135537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2481 : Bounds (5058183 / 62500000) (80930929 / 1000000000) (Real.log (135537 / 125000)) := by
  have h := reflection_log_2481_neg
  have he : Real.log (135537 / 125000) = -Real.log (125000 / 135537) := by
    rw [show ((135537 / 125000) : ℝ) = ((125000 / 135537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2482_neg : (8806211 / 100000000) ≤ -Real.log (114463 / 125000) ∧
    -Real.log (114463 / 125000) ≤ (88062111 / 1000000000) := by
  have h := checkLog_sound (w := (10537 / 239463)) (n := 12)
    (lo := (8806211 / 100000000)) (hi := (88062111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 114463) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 114463) = 1/(114463 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2482 : Bounds (-88062111 / 1000000000) (-8806211 / 100000000) (Real.log (114463 / 125000)) := by
  have h := reflection_log_2482_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2483_neg : (40566441 / 500000000) ≤ -Real.log (200000 / 216903) ∧
    -Real.log (200000 / 216903) ≤ (81132883 / 1000000000) := by
  have h := checkLog_sound (w := (16903 / 416903)) (n := 12)
    (lo := (40566441 / 500000000)) (hi := (81132883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216903 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216903 / 200000) = 1/(200000 / 216903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2483 : Bounds (40566441 / 500000000) (81132883 / 1000000000) (Real.log (216903 / 200000)) := by
  have h := reflection_log_2483_neg
  have he : Real.log (216903 / 200000) = -Real.log (200000 / 216903) := by
    rw [show ((216903 / 200000) : ℝ) = ((200000 / 216903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2484_neg : (88301299 / 1000000000) ≤ -Real.log (183097 / 200000) ∧
    -Real.log (183097 / 200000) ≤ (883013 / 10000000) := by
  have h := checkLog_sound (w := (16903 / 383097)) (n := 12)
    (lo := (88301299 / 1000000000)) (hi := (883013 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183097) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183097) = 1/(183097 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2484 : Bounds (-883013 / 10000000) (-88301299 / 1000000000) (Real.log (183097 / 200000)) := by
  have h := reflection_log_2484_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2485_neg : (7168417 / 1000000000) ≤ -Real.log (39714288591 / 40000000000) ∧
    -Real.log (39714288591 / 40000000000) ≤ (3584209 / 500000000) := by
  have h := checkLog_sound (w := (285711409 / 79714288591)) (n := 12)
    (lo := (7168417 / 1000000000)) (hi := (3584209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39714288591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39714288591) = 1/(39714288591 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2485 : Bounds (-3584209 / 500000000) (-7168417 / 1000000000) (Real.log (39714288591 / 40000000000)) := by
  have h := reflection_log_2485_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2486_neg : (3565591 / 500000000) ≤ -Real.log (15513971631 / 15625000000) ∧
    -Real.log (15513971631 / 15625000000) ≤ (7131183 / 1000000000) := by
  have h := checkLog_sound (w := (111028369 / 31138971631)) (n := 12)
    (lo := (3565591 / 500000000)) (hi := (7131183 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15513971631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15513971631) = 1/(15513971631 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2486 : Bounds (-7131183 / 1000000000) (-3565591 / 500000000) (Real.log (15513971631 / 15625000000)) := by
  have h := reflection_log_2486_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2487_neg : (168993039 / 1000000000) ≤ -Real.log (50000000000 / 59205594821) ∧
    -Real.log (50000000000 / 59205594821) ≤ (2112413 / 12500000) := by
  have h := checkLog_sound (w := (9205594821 / 109205594821)) (n := 12)
    (lo := (168993039 / 1000000000)) (hi := (2112413 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59205594821 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59205594821 / 50000000000) = 1/(50000000000 / 59205594821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2487 : Bounds (168993039 / 1000000000) (2112413 / 12500000) (Real.log (59205594821 / 50000000000)) := by
  have h := reflection_log_2487_neg
  have he : Real.log (59205594821 / 50000000000) = -Real.log (50000000000 / 59205594821) := by
    rw [show ((59205594821 / 50000000000) : ℝ) = ((50000000000 / 59205594821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2488_neg : (169434181 / 1000000000) ≤ -Real.log (100000000000 / 118463437413) ∧
    -Real.log (100000000000 / 118463437413) ≤ (84717091 / 500000000) := by
  have h := checkLog_sound (w := (18463437413 / 218463437413)) (n := 12)
    (lo := (169434181 / 1000000000)) (hi := (84717091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118463437413 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118463437413 / 100000000000) = 1/(100000000000 / 118463437413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2488 : Bounds (169434181 / 1000000000) (84717091 / 500000000) (Real.log (118463437413 / 100000000000)) := by
  have h := reflection_log_2488_neg
  have he : Real.log (118463437413 / 100000000000) = -Real.log (100000000000 / 118463437413) := by
    rw [show ((118463437413 / 100000000000) : ℝ) = ((100000000000 / 118463437413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2489_neg : (339009917 / 1000000000) ≤ -Real.log (4000000000 / 5614229059) ∧
    -Real.log (4000000000 / 5614229059) ≤ (169504959 / 500000000) := by
  have h := checkLog_sound (w := (1614229059 / 9614229059)) (n := 12)
    (lo := (339009917 / 1000000000)) (hi := (169504959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5614229059 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5614229059 / 4000000000) = 1/(4000000000 / 5614229059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2489 : Bounds (339009917 / 1000000000) (169504959 / 500000000) (Real.log (5614229059 / 4000000000)) := by
  have h := reflection_log_2489_neg
  have he : Real.log (5614229059 / 4000000000) = -Real.log (4000000000 / 5614229059) := by
    rw [show ((5614229059 / 4000000000) : ℝ) = ((4000000000 / 5614229059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2490_neg : (169607861 / 500000000) ≤ -Real.log (125000000000 / 175480769231) ∧
    -Real.log (125000000000 / 175480769231) ≤ (339215723 / 1000000000) := by
  have h := checkLog_sound (w := (50480769231 / 300480769231)) (n := 12)
    (lo := (169607861 / 500000000)) (hi := (339215723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175480769231 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175480769231 / 125000000000) = 1/(125000000000 / 175480769231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2490 : Bounds (169607861 / 500000000) (339215723 / 1000000000) (Real.log (175480769231 / 125000000000)) := by
  have h := reflection_log_2490_neg
  have he : Real.log (175480769231 / 125000000000) = -Real.log (125000000000 / 175480769231) := by
    rw [show ((175480769231 / 125000000000) : ℝ) = ((125000000000 / 175480769231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2491_neg : (155378497 / 1000000000) ≤ -Real.log (10000 / 11681) ∧
    -Real.log (10000 / 11681) ≤ (77689249 / 500000000) := by
  have h := checkLog_sound (w := (1681 / 21681)) (n := 12)
    (lo := (155378497 / 1000000000)) (hi := (77689249 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11681 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11681 / 10000) = 1/(10000 / 11681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2491 : Bounds (155378497 / 1000000000) (77689249 / 500000000) (Real.log (11681 / 10000)) := by
  have h := reflection_log_2491_neg
  have he : Real.log (11681 / 10000) = -Real.log (10000 / 11681) := by
    rw [show ((11681 / 10000) : ℝ) = ((10000 / 11681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2492_neg : (184043037 / 1000000000) ≤ -Real.log (8319 / 10000) ∧
    -Real.log (8319 / 10000) ≤ (92021519 / 500000000) := by
  have h := checkLog_sound (w := (1681 / 18319)) (n := 12)
    (lo := (184043037 / 1000000000)) (hi := (92021519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8319) = 1/(8319 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2492 : Bounds (-92021519 / 500000000) (-184043037 / 1000000000) (Real.log (8319 / 10000)) := by
  have h := reflection_log_2492_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2493_neg : (33617 / 200000000) ≤ -Real.log (10000000 / 10001681) ∧
    -Real.log (10000000 / 10001681) ≤ (84043 / 500000000) := by
  have h := checkLog_sound (w := (1681 / 20001681)) (n := 12)
    (lo := (33617 / 200000000)) (hi := (84043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001681 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001681 / 10000000) = 1/(10000000 / 10001681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2493 : Bounds (33617 / 200000000) (84043 / 500000000) (Real.log (10001681 / 10000000)) := by
  have h := reflection_log_2493_neg
  have he : Real.log (10001681 / 10000000) = -Real.log (10000000 / 10001681) := by
    rw [show ((10001681 / 10000000) : ℝ) = ((10000000 / 10001681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2494_neg : (84057 / 500000000) ≤ -Real.log (9998319 / 10000000) ∧
    -Real.log (9998319 / 10000000) ≤ (33623 / 200000000) := by
  have h := checkLog_sound (w := (1681 / 19998319)) (n := 12)
    (lo := (84057 / 500000000)) (hi := (33623 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998319) = 1/(9998319 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2494 : Bounds (-33623 / 200000000) (-84057 / 500000000) (Real.log (9998319 / 10000000)) := by
  have h := reflection_log_2494_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2495_neg : (40488981 / 500000000) ≤ -Real.log (1000000 / 1084347) ∧
    -Real.log (1000000 / 1084347) ≤ (80977963 / 1000000000) := by
  have h := checkLog_sound (w := (84347 / 2084347)) (n := 12)
    (lo := (40488981 / 500000000)) (hi := (80977963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084347 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084347 / 1000000) = 1/(1000000 / 1084347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2495 : Bounds (40488981 / 500000000) (80977963 / 1000000000) (Real.log (1084347 / 1000000)) := by
  have h := reflection_log_2495_neg
  have he : Real.log (1084347 / 1000000) = -Real.log (1000000 / 1084347) := by
    rw [show ((1084347 / 1000000) : ℝ) = ((1000000 / 1084347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
