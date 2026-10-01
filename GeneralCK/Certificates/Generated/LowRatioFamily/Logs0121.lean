import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7744_neg : (121845651 / 1000000000) ≤ -Real.log (177057 / 200000) ∧
    -Real.log (177057 / 200000) ≤ (30461413 / 250000000) := by
  have h := checkLog_sound (w := (22943 / 377057)) (n := 12)
    (lo := (121845651 / 1000000000)) (hi := (30461413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 177057) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 177057) = 1/(177057 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7744 : Bounds (-30461413 / 250000000) (-121845651 / 1000000000) (Real.log (177057 / 200000)) := by
  have h := reflection_log_7744_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7745_neg : (3407277 / 31250000) ≤ -Real.log (1000000 / 1115199) ∧
    -Real.log (1000000 / 1115199) ≤ (21806573 / 200000000) := by
  have h := checkLog_sound (w := (115199 / 2115199)) (n := 12)
    (lo := (3407277 / 31250000)) (hi := (21806573 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1115199 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1115199 / 1000000) = 1/(1000000 / 1115199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7745 : Bounds (3407277 / 31250000) (21806573 / 200000000) (Real.log (1115199 / 1000000)) := by
  have h := reflection_log_7745_neg
  have he : Real.log (1115199 / 1000000) = -Real.log (1000000 / 1115199) := by
    rw [show ((1115199 / 1000000) : ℝ) = ((1000000 / 1115199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7746_neg : (61196259 / 500000000) ≤ -Real.log (884801 / 1000000) ∧
    -Real.log (884801 / 1000000) ≤ (122392519 / 1000000000) := by
  have h := checkLog_sound (w := (115199 / 1884801)) (n := 12)
    (lo := (61196259 / 500000000)) (hi := (122392519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 884801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 884801) = 1/(884801 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7746 : Bounds (-122392519 / 1000000000) (-61196259 / 500000000) (Real.log (884801 / 1000000)) := by
  have h := reflection_log_7746_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7747_neg : (13359653 / 1000000000) ≤ -Real.log (986729190399 / 1000000000000) ∧
    -Real.log (986729190399 / 1000000000000) ≤ (6679827 / 500000000) := by
  have h := checkLog_sound (w := (13270809601 / 1986729190399)) (n := 12)
    (lo := (13359653 / 1000000000)) (hi := (6679827 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986729190399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986729190399) = 1/(986729190399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7747 : Bounds (-6679827 / 500000000) (-13359653 / 1000000000) (Real.log (986729190399 / 1000000000000)) := by
  have h := reflection_log_7747_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7748_neg : (2649377 / 200000000) ≤ -Real.log (39473618751 / 40000000000) ∧
    -Real.log (39473618751 / 40000000000) ≤ (6623443 / 500000000) := by
  have h := checkLog_sound (w := (526381249 / 79473618751)) (n := 12)
    (lo := (2649377 / 200000000)) (hi := (6623443 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39473618751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39473618751) = 1/(39473618751 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7748 : Bounds (-6623443 / 500000000) (-2649377 / 200000000) (Real.log (39473618751 / 40000000000)) := by
  have h := reflection_log_7748_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7749_neg : (115222209 / 500000000) ≤ -Real.log (500000000000 / 629579739857) ∧
    -Real.log (500000000000 / 629579739857) ≤ (230444419 / 1000000000) := by
  have h := checkLog_sound (w := (129579739857 / 1129579739857)) (n := 12)
    (lo := (115222209 / 500000000)) (hi := (230444419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((629579739857 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(629579739857 / 500000000000) = 1/(500000000000 / 629579739857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7749 : Bounds (115222209 / 500000000) (230444419 / 1000000000) (Real.log (629579739857 / 500000000000)) := by
  have h := reflection_log_7749_neg
  have he : Real.log (629579739857 / 500000000000) = -Real.log (500000000000 / 629579739857) := by
    rw [show ((629579739857 / 500000000000) : ℝ) = ((500000000000 / 629579739857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7750_neg : (115712691 / 500000000) ≤ -Real.log (500000000000 / 630197637661) ∧
    -Real.log (500000000000 / 630197637661) ≤ (231425383 / 1000000000) := by
  have h := checkLog_sound (w := (130197637661 / 1130197637661)) (n := 12)
    (lo := (115712691 / 500000000)) (hi := (231425383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630197637661 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(630197637661 / 500000000000) = 1/(500000000000 / 630197637661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7750 : Bounds (115712691 / 500000000) (231425383 / 1000000000) (Real.log (630197637661 / 500000000000)) := by
  have h := reflection_log_7750_neg
  have he : Real.log (630197637661 / 500000000000) = -Real.log (500000000000 / 630197637661) := by
    rw [show ((630197637661 / 500000000000) : ℝ) = ((500000000000 / 630197637661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7751_neg : (9262057 / 20000000) ≤ -Real.log (500000000000 / 794498381877) ∧
    -Real.log (500000000000 / 794498381877) ≤ (463102851 / 1000000000) := by
  have h := checkLog_sound (w := (294498381877 / 1294498381877)) (n := 12)
    (lo := (9262057 / 20000000)) (hi := (463102851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((794498381877 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(794498381877 / 500000000000) = 1/(500000000000 / 794498381877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7751 : Bounds (9262057 / 20000000) (463102851 / 1000000000) (Real.log (794498381877 / 500000000000)) := by
  have h := reflection_log_7751_neg
  have he : Real.log (794498381877 / 500000000000) = -Real.log (500000000000 / 794498381877) := by
    rw [show ((794498381877 / 500000000000) : ℝ) = ((500000000000 / 794498381877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7752_neg : (232078779 / 500000000) ≤ -Real.log (100000000000 / 159067357513) ∧
    -Real.log (100000000000 / 159067357513) ≤ (464157559 / 1000000000) := by
  have h := checkLog_sound (w := (59067357513 / 259067357513)) (n := 12)
    (lo := (232078779 / 500000000)) (hi := (464157559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159067357513 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159067357513 / 100000000000) = 1/(100000000000 / 159067357513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7752 : Bounds (232078779 / 500000000) (464157559 / 1000000000) (Real.log (159067357513 / 100000000000)) := by
  have h := reflection_log_7752_neg
  have he : Real.log (159067357513 / 100000000000) = -Real.log (100000000000 / 159067357513) := by
    rw [show ((159067357513 / 100000000000) : ℝ) = ((100000000000 / 159067357513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7753_neg : (25724239 / 125000000) ≤ -Real.log (2000 / 2457) ∧
    -Real.log (2000 / 2457) ≤ (205793913 / 1000000000) := by
  have h := checkLog_sound (w := (457 / 4457)) (n := 12)
    (lo := (25724239 / 125000000)) (hi := (205793913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2457 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2457 / 2000) = 1/(2000 / 2457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7753 : Bounds (25724239 / 125000000) (205793913 / 1000000000) (Real.log (2457 / 2000)) := by
  have h := reflection_log_7753_neg
  have he : Real.log (2457 / 2000) = -Real.log (2000 / 2457) := by
    rw [show ((2457 / 2000) : ℝ) = ((2000 / 2457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7754_neg : (259418607 / 1000000000) ≤ -Real.log (1543 / 2000) ∧
    -Real.log (1543 / 2000) ≤ (16213663 / 62500000) := by
  have h := checkLog_sound (w := (457 / 3543)) (n := 12)
    (lo := (259418607 / 1000000000)) (hi := (16213663 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1543) = 1/(1543 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7754 : Bounds (-16213663 / 62500000) (-259418607 / 1000000000) (Real.log (1543 / 2000)) := by
  have h := reflection_log_7754_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7755_neg : (228473 / 1000000000) ≤ -Real.log (2000000 / 2000457) ∧
    -Real.log (2000000 / 2000457) ≤ (114237 / 500000000) := by
  have h := checkLog_sound (w := (457 / 4000457)) (n := 12)
    (lo := (228473 / 1000000000)) (hi := (114237 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000457 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000457 / 2000000) = 1/(2000000 / 2000457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7755 : Bounds (228473 / 1000000000) (114237 / 500000000) (Real.log (2000457 / 2000000)) := by
  have h := reflection_log_7755_neg
  have he : Real.log (2000457 / 2000000) = -Real.log (2000000 / 2000457) := by
    rw [show ((2000457 / 2000000) : ℝ) = ((2000000 / 2000457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7756_neg : (114263 / 500000000) ≤ -Real.log (1999543 / 2000000) ∧
    -Real.log (1999543 / 2000000) ≤ (228527 / 1000000000) := by
  have h := checkLog_sound (w := (457 / 3999543)) (n := 12)
    (lo := (114263 / 500000000)) (hi := (228527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999543) = 1/(1999543 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7756 : Bounds (-228527 / 1000000000) (-114263 / 500000000) (Real.log (1999543 / 2000000)) := by
  have h := reflection_log_7756_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7757_neg : (27207323 / 250000000) ≤ -Real.log (250000 / 278743) ∧
    -Real.log (250000 / 278743) ≤ (108829293 / 1000000000) := by
  have h := checkLog_sound (w := (28743 / 528743)) (n := 12)
    (lo := (27207323 / 250000000)) (hi := (108829293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((278743 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(278743 / 250000) = 1/(250000 / 278743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7757 : Bounds (27207323 / 250000000) (108829293 / 1000000000) (Real.log (278743 / 250000)) := by
  have h := reflection_log_7757_neg
  have he : Real.log (278743 / 250000) = -Real.log (250000 / 278743) := by
    rw [show ((278743 / 250000) : ℝ) = ((250000 / 278743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7758_neg : (30533999 / 250000000) ≤ -Real.log (221257 / 250000) ∧
    -Real.log (221257 / 250000) ≤ (122135997 / 1000000000) := by
  have h := checkLog_sound (w := (28743 / 471257)) (n := 12)
    (lo := (30533999 / 250000000)) (hi := (122135997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 221257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 221257) = 1/(221257 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7758 : Bounds (-122135997 / 1000000000) (-30533999 / 250000000) (Real.log (221257 / 250000)) := by
  have h := reflection_log_7758_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7759_neg : (109263289 / 1000000000) ≤ -Real.log (15625 / 17429) ∧
    -Real.log (15625 / 17429) ≤ (10926329 / 100000000) := by
  have h := checkLog_sound (w := (902 / 16527)) (n := 12)
    (lo := (109263289 / 1000000000)) (hi := (10926329 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17429 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17429 / 15625) = 1/(15625 / 17429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7759 : Bounds (109263289 / 1000000000) (10926329 / 100000000) (Real.log (17429 / 15625)) := by
  have h := reflection_log_7759_neg
  have he : Real.log (17429 / 15625) = -Real.log (15625 / 17429) := by
    rw [show ((17429 / 15625) : ℝ) = ((15625 / 17429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7760_neg : (122683021 / 1000000000) ≤ -Real.log (13821 / 15625) ∧
    -Real.log (13821 / 15625) ≤ (61341511 / 500000000) := by
  have h := checkLog_sound (w := (902 / 14723)) (n := 12)
    (lo := (122683021 / 1000000000)) (hi := (61341511 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 13821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 13821) = 1/(13821 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7760 : Bounds (-61341511 / 500000000) (-122683021 / 1000000000) (Real.log (13821 / 15625)) := by
  have h := reflection_log_7760_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7761_neg : (13419731 / 1000000000) ≤ -Real.log (240886209 / 244140625) ∧
    -Real.log (240886209 / 244140625) ≤ (3354933 / 250000000) := by
  have h := checkLog_sound (w := (1627208 / 242513417)) (n := 12)
    (lo := (13419731 / 1000000000)) (hi := (3354933 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 240886209) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 240886209) = 1/(240886209 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7761 : Bounds (-3354933 / 250000000) (-13419731 / 1000000000) (Real.log (240886209 / 244140625)) := by
  have h := reflection_log_7761_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7762_neg : (13306703 / 1000000000) ≤ -Real.log (61673839951 / 62500000000) ∧
    -Real.log (61673839951 / 62500000000) ≤ (831669 / 62500000) := by
  have h := checkLog_sound (w := (826160049 / 124173839951)) (n := 12)
    (lo := (13306703 / 1000000000)) (hi := (831669 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61673839951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61673839951) = 1/(61673839951 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7762 : Bounds (-831669 / 62500000) (-13306703 / 1000000000) (Real.log (61673839951 / 62500000000)) := by
  have h := reflection_log_7762_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7763_neg : (28870661 / 125000000) ≤ -Real.log (50000000000 / 62990775433) ∧
    -Real.log (50000000000 / 62990775433) ≤ (230965289 / 1000000000) := by
  have h := checkLog_sound (w := (12990775433 / 112990775433)) (n := 12)
    (lo := (28870661 / 125000000)) (hi := (230965289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62990775433 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62990775433 / 50000000000) = 1/(50000000000 / 62990775433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7763 : Bounds (28870661 / 125000000) (230965289 / 1000000000) (Real.log (62990775433 / 50000000000)) := by
  have h := reflection_log_7763_neg
  have he : Real.log (62990775433 / 50000000000) = -Real.log (50000000000 / 62990775433) := by
    rw [show ((62990775433 / 50000000000) : ℝ) = ((50000000000 / 62990775433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7764_neg : (23194631 / 100000000) ≤ -Real.log (500000000000 / 630526011143) ∧
    -Real.log (500000000000 / 630526011143) ≤ (231946311 / 1000000000) := by
  have h := checkLog_sound (w := (130526011143 / 1130526011143)) (n := 12)
    (lo := (23194631 / 100000000)) (hi := (231946311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630526011143 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(630526011143 / 500000000000) = 1/(500000000000 / 630526011143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7764 : Bounds (23194631 / 100000000) (231946311 / 1000000000) (Real.log (630526011143 / 500000000000)) := by
  have h := reflection_log_7764_neg
  have he : Real.log (630526011143 / 500000000000) = -Real.log (500000000000 / 630526011143) := by
    rw [show ((630526011143 / 500000000000) : ℝ) = ((500000000000 / 630526011143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7765_neg : (232078779 / 500000000) ≤ -Real.log (125000000000 / 198834196891) ∧
    -Real.log (125000000000 / 198834196891) ≤ (464157559 / 1000000000) := by
  have h := checkLog_sound (w := (73834196891 / 323834196891)) (n := 12)
    (lo := (232078779 / 500000000)) (hi := (464157559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((198834196891 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(198834196891 / 125000000000) = 1/(125000000000 / 198834196891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7765 : Bounds (232078779 / 500000000) (464157559 / 1000000000) (Real.log (198834196891 / 125000000000)) := by
  have h := reflection_log_7765_neg
  have he : Real.log (198834196891 / 125000000000) = -Real.log (125000000000 / 198834196891) := by
    rw [show ((198834196891 / 125000000000) : ℝ) = ((125000000000 / 198834196891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7766_neg : (11630313 / 25000000) ≤ -Real.log (20000000000 / 31847051199) ∧
    -Real.log (20000000000 / 31847051199) ≤ (465212521 / 1000000000) := by
  have h := checkLog_sound (w := (11847051199 / 51847051199)) (n := 12)
    (lo := (11630313 / 25000000)) (hi := (465212521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31847051199 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31847051199 / 20000000000) = 1/(20000000000 / 31847051199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7766 : Bounds (11630313 / 25000000) (465212521 / 1000000000) (Real.log (31847051199 / 20000000000)) := by
  have h := reflection_log_7766_neg
  have he : Real.log (31847051199 / 20000000000) = -Real.log (20000000000 / 31847051199) := by
    rw [show ((31847051199 / 20000000000) : ℝ) = ((20000000000 / 31847051199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7767_neg : (20620083 / 100000000) ≤ -Real.log (1000 / 1229) ∧
    -Real.log (1000 / 1229) ≤ (206200831 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 2229)) (n := 12)
    (lo := (20620083 / 100000000)) (hi := (206200831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1229 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1229 / 1000) = 1/(1000 / 1229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7767 : Bounds (20620083 / 100000000) (206200831 / 1000000000) (Real.log (1229 / 1000)) := by
  have h := reflection_log_7767_neg
  have he : Real.log (1229 / 1000) = -Real.log (1000 / 1229) := by
    rw [show ((1229 / 1000) : ℝ) = ((1000 / 1229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7768_neg : (52013381 / 200000000) ≤ -Real.log (771 / 1000) ∧
    -Real.log (771 / 1000) ≤ (130033453 / 500000000) := by
  have h := checkLog_sound (w := (229 / 1771)) (n := 12)
    (lo := (52013381 / 200000000)) (hi := (130033453 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 771) = 1/(771 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7768 : Bounds (-130033453 / 500000000) (-52013381 / 200000000) (Real.log (771 / 1000)) := by
  have h := reflection_log_7768_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7769_neg : (228973 / 1000000000) ≤ -Real.log (1000000 / 1000229) ∧
    -Real.log (1000000 / 1000229) ≤ (114487 / 500000000) := by
  have h := checkLog_sound (w := (229 / 2000229)) (n := 12)
    (lo := (228973 / 1000000000)) (hi := (114487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000229 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000229 / 1000000) = 1/(1000000 / 1000229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7769 : Bounds (228973 / 1000000000) (114487 / 500000000) (Real.log (1000229 / 1000000)) := by
  have h := reflection_log_7769_neg
  have he : Real.log (1000229 / 1000000) = -Real.log (1000000 / 1000229) := by
    rw [show ((1000229 / 1000000) : ℝ) = ((1000000 / 1000229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7770_neg : (114513 / 500000000) ≤ -Real.log (999771 / 1000000) ∧
    -Real.log (999771 / 1000000) ≤ (229027 / 1000000000) := by
  have h := checkLog_sound (w := (229 / 1999771)) (n := 12)
    (lo := (114513 / 500000000)) (hi := (229027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999771) = 1/(999771 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7770 : Bounds (-229027 / 1000000000) (-114513 / 500000000) (Real.log (999771 / 1000000)) := by
  have h := reflection_log_7770_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7771_neg : (27264941 / 250000000) ≤ -Real.log (1000000 / 1115229) ∧
    -Real.log (1000000 / 1115229) ≤ (21811953 / 200000000) := by
  have h := checkLog_sound (w := (115229 / 2115229)) (n := 12)
    (lo := (27264941 / 250000000)) (hi := (21811953 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1115229 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1115229 / 1000000) = 1/(1000000 / 1115229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7771 : Bounds (27264941 / 250000000) (21811953 / 200000000) (Real.log (1115229 / 1000000)) := by
  have h := reflection_log_7771_neg
  have he : Real.log (1115229 / 1000000) = -Real.log (1000000 / 1115229) := by
    rw [show ((1115229 / 1000000) : ℝ) = ((1000000 / 1115229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7772_neg : (15303303 / 125000000) ≤ -Real.log (884771 / 1000000) ∧
    -Real.log (884771 / 1000000) ≤ (4897057 / 40000000) := by
  have h := checkLog_sound (w := (115229 / 1884771)) (n := 12)
    (lo := (15303303 / 125000000)) (hi := (4897057 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 884771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 884771) = 1/(884771 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7772 : Bounds (-4897057 / 40000000) (-15303303 / 125000000) (Real.log (884771 / 1000000)) := by
  have h := reflection_log_7772_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7773_neg : (54747279 / 500000000) ≤ -Real.log (500000 / 557857) ∧
    -Real.log (500000 / 557857) ≤ (109494559 / 1000000000) := by
  have h := checkLog_sound (w := (57857 / 1057857)) (n := 12)
    (lo := (54747279 / 500000000)) (hi := (109494559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((557857 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(557857 / 500000) = 1/(500000 / 557857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7773 : Bounds (54747279 / 500000000) (109494559 / 1000000000) (Real.log (557857 / 500000)) := by
  have h := reflection_log_7773_neg
  have he : Real.log (557857 / 500000) = -Real.log (500000 / 557857) := by
    rw [show ((557857 / 500000) : ℝ) = ((500000 / 557857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7774_neg : (122974739 / 1000000000) ≤ -Real.log (442143 / 500000) ∧
    -Real.log (442143 / 500000) ≤ (6148737 / 50000000) := by
  have h := checkLog_sound (w := (57857 / 942143)) (n := 12)
    (lo := (122974739 / 1000000000)) (hi := (6148737 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 442143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 442143) = 1/(442143 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7774 : Bounds (-6148737 / 50000000) (-122974739 / 1000000000) (Real.log (442143 / 500000)) := by
  have h := reflection_log_7774_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7775_neg : (674009 / 50000000) ≤ -Real.log (246652567551 / 250000000000) ∧
    -Real.log (246652567551 / 250000000000) ≤ (13480181 / 1000000000) := by
  have h := checkLog_sound (w := (3347432449 / 496652567551)) (n := 12)
    (lo := (674009 / 50000000)) (hi := (13480181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246652567551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246652567551) = 1/(246652567551 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7775 : Bounds (-13480181 / 1000000000) (-674009 / 50000000) (Real.log (246652567551 / 250000000000)) := by
  have h := reflection_log_7775_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7776_neg : (13366659 / 1000000000) ≤ -Real.log (986722277559 / 1000000000000) ∧
    -Real.log (986722277559 / 1000000000000) ≤ (668333 / 50000000) := by
  have h := checkLog_sound (w := (13277722441 / 1986722277559)) (n := 12)
    (lo := (13366659 / 1000000000)) (hi := (668333 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986722277559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986722277559) = 1/(986722277559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7776 : Bounds (-668333 / 50000000) (-13366659 / 1000000000) (Real.log (986722277559 / 1000000000000)) := by
  have h := reflection_log_7776_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7777_neg : (231486189 / 1000000000) ≤ -Real.log (500000000000 / 630235959361) ∧
    -Real.log (500000000000 / 630235959361) ≤ (23148619 / 100000000) := by
  have h := checkLog_sound (w := (130235959361 / 1130235959361)) (n := 12)
    (lo := (231486189 / 1000000000)) (hi := (23148619 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630235959361 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(630235959361 / 500000000000) = 1/(500000000000 / 630235959361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7777 : Bounds (231486189 / 1000000000) (23148619 / 100000000) (Real.log (630235959361 / 500000000000)) := by
  have h := reflection_log_7777_neg
  have he : Real.log (630235959361 / 500000000000) = -Real.log (500000000000 / 630235959361) := by
    rw [show ((630235959361 / 500000000000) : ℝ) = ((500000000000 / 630235959361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7778_neg : (232469297 / 1000000000) ≤ -Real.log (62500000000 / 78856981791) ∧
    -Real.log (62500000000 / 78856981791) ≤ (116234649 / 500000000) := by
  have h := checkLog_sound (w := (16356981791 / 141356981791)) (n := 12)
    (lo := (232469297 / 1000000000)) (hi := (116234649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78856981791 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78856981791 / 62500000000) = 1/(62500000000 / 78856981791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7778 : Bounds (232469297 / 1000000000) (116234649 / 500000000) (Real.log (78856981791 / 62500000000)) := by
  have h := reflection_log_7778_neg
  have he : Real.log (78856981791 / 62500000000) = -Real.log (62500000000 / 78856981791) := by
    rw [show ((78856981791 / 62500000000) : ℝ) = ((62500000000 / 78856981791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7779_neg : (11630313 / 25000000) ≤ -Real.log (250000000000 / 398088139987) ∧
    -Real.log (250000000000 / 398088139987) ≤ (465212521 / 1000000000) := by
  have h := checkLog_sound (w := (148088139987 / 648088139987)) (n := 12)
    (lo := (11630313 / 25000000)) (hi := (465212521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((398088139987 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(398088139987 / 250000000000) = 1/(250000000000 / 398088139987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7779 : Bounds (11630313 / 25000000) (465212521 / 1000000000) (Real.log (398088139987 / 250000000000)) := by
  have h := reflection_log_7779_neg
  have he : Real.log (398088139987 / 250000000000) = -Real.log (250000000000 / 398088139987) := by
    rw [show ((398088139987 / 250000000000) : ℝ) = ((250000000000 / 398088139987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7780_neg : (58283467 / 125000000) ≤ -Real.log (25000000000 / 39850843061) ∧
    -Real.log (25000000000 / 39850843061) ≤ (466267737 / 1000000000) := by
  have h := checkLog_sound (w := (14850843061 / 64850843061)) (n := 12)
    (lo := (58283467 / 125000000)) (hi := (466267737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39850843061 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39850843061 / 25000000000) = 1/(25000000000 / 39850843061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7780 : Bounds (58283467 / 125000000) (466267737 / 1000000000) (Real.log (39850843061 / 25000000000)) := by
  have h := reflection_log_7780_neg
  have he : Real.log (39850843061 / 25000000000) = -Real.log (25000000000 / 39850843061) := by
    rw [show ((39850843061 / 25000000000) : ℝ) = ((25000000000 / 39850843061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7781_neg : (103303791 / 500000000) ≤ -Real.log (2000 / 2459) ∧
    -Real.log (2000 / 2459) ≤ (206607583 / 1000000000) := by
  have h := checkLog_sound (w := (459 / 4459)) (n := 12)
    (lo := (103303791 / 500000000)) (hi := (206607583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2459 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2459 / 2000) = 1/(2000 / 2459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7781 : Bounds (103303791 / 500000000) (206607583 / 1000000000) (Real.log (2459 / 2000)) := by
  have h := reflection_log_7781_neg
  have he : Real.log (2459 / 2000) = -Real.log (2000 / 2459) := by
    rw [show ((2459 / 2000) : ℝ) = ((2000 / 2459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7782_neg : (32589453 / 125000000) ≤ -Real.log (1541 / 2000) ∧
    -Real.log (1541 / 2000) ≤ (83429 / 320000) := by
  have h := checkLog_sound (w := (459 / 3541)) (n := 12)
    (lo := (32589453 / 125000000)) (hi := (83429 / 320000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1541) = 1/(1541 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7782 : Bounds (-83429 / 320000) (-32589453 / 125000000) (Real.log (1541 / 2000)) := by
  have h := reflection_log_7782_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7783_neg : (229473 / 1000000000) ≤ -Real.log (2000000 / 2000459) ∧
    -Real.log (2000000 / 2000459) ≤ (114737 / 500000000) := by
  have h := checkLog_sound (w := (459 / 4000459)) (n := 12)
    (lo := (229473 / 1000000000)) (hi := (114737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000459 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000459 / 2000000) = 1/(2000000 / 2000459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7783 : Bounds (229473 / 1000000000) (114737 / 500000000) (Real.log (2000459 / 2000000)) := by
  have h := reflection_log_7783_neg
  have he : Real.log (2000459 / 2000000) = -Real.log (2000000 / 2000459) := by
    rw [show ((2000459 / 2000000) : ℝ) = ((2000000 / 2000459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7784_neg : (114763 / 500000000) ≤ -Real.log (1999541 / 2000000) ∧
    -Real.log (1999541 / 2000000) ≤ (229527 / 1000000000) := by
  have h := checkLog_sound (w := (459 / 3999541)) (n := 12)
    (lo := (114763 / 500000000)) (hi := (229527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999541) = 1/(1999541 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7784 : Bounds (-229527 / 1000000000) (-114763 / 500000000) (Real.log (1999541 / 2000000)) := by
  have h := reflection_log_7784_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7785_neg : (13661273 / 125000000) ≤ -Real.log (500000 / 557743) ∧
    -Real.log (500000 / 557743) ≤ (21858037 / 200000000) := by
  have h := checkLog_sound (w := (57743 / 1057743)) (n := 12)
    (lo := (13661273 / 125000000)) (hi := (21858037 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((557743 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(557743 / 500000) = 1/(500000 / 557743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7785 : Bounds (13661273 / 125000000) (21858037 / 200000000) (Real.log (557743 / 500000)) := by
  have h := reflection_log_7785_neg
  have he : Real.log (557743 / 500000) = -Real.log (500000 / 557743) := by
    rw [show ((557743 / 500000) : ℝ) = ((500000 / 557743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7786_neg : (122716937 / 1000000000) ≤ -Real.log (442257 / 500000) ∧
    -Real.log (442257 / 500000) ≤ (61358469 / 500000000) := by
  have h := checkLog_sound (w := (57743 / 942257)) (n := 12)
    (lo := (122716937 / 1000000000)) (hi := (61358469 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 442257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 442257) = 1/(442257 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7786 : Bounds (-61358469 / 500000000) (-122716937 / 1000000000) (Real.log (442257 / 500000)) := by
  have h := reflection_log_7786_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7787_neg : (109724877 / 1000000000) ≤ -Real.log (1000000 / 1115971) ∧
    -Real.log (1000000 / 1115971) ≤ (54862439 / 500000000) := by
  have h := checkLog_sound (w := (115971 / 2115971)) (n := 12)
    (lo := (109724877 / 1000000000)) (hi := (54862439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1115971 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1115971 / 1000000) = 1/(1000000 / 1115971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7787 : Bounds (109724877 / 1000000000) (54862439 / 500000000) (Real.log (1115971 / 1000000)) := by
  have h := reflection_log_7787_neg
  have he : Real.log (1115971 / 1000000) = -Real.log (1000000 / 1115971) := by
    rw [show ((1115971 / 1000000) : ℝ) = ((1000000 / 1115971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7788_neg : (123265411 / 1000000000) ≤ -Real.log (884029 / 1000000) ∧
    -Real.log (884029 / 1000000) ≤ (30816353 / 250000000) := by
  have h := checkLog_sound (w := (115971 / 1884029)) (n := 12)
    (lo := (123265411 / 1000000000)) (hi := (30816353 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 884029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 884029) = 1/(884029 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7788 : Bounds (-30816353 / 250000000) (-123265411 / 1000000000) (Real.log (884029 / 1000000)) := by
  have h := reflection_log_7788_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7789_neg : (13540533 / 1000000000) ≤ -Real.log (986550727159 / 1000000000000) ∧
    -Real.log (986550727159 / 1000000000000) ≤ (6770267 / 500000000) := by
  have h := checkLog_sound (w := (13449272841 / 1986550727159)) (n := 12)
    (lo := (13540533 / 1000000000)) (hi := (6770267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986550727159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986550727159) = 1/(986550727159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7789 : Bounds (-6770267 / 500000000) (-13540533 / 1000000000) (Real.log (986550727159 / 1000000000000)) := by
  have h := reflection_log_7789_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7790_neg : (209793 / 15625000) ≤ -Real.log (246665745951 / 250000000000) ∧
    -Real.log (246665745951 / 250000000000) ≤ (13426753 / 1000000000) := by
  have h := checkLog_sound (w := (3334254049 / 496665745951)) (n := 12)
    (lo := (209793 / 15625000)) (hi := (13426753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246665745951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246665745951) = 1/(246665745951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7790 : Bounds (-13426753 / 1000000000) (-209793 / 15625000) (Real.log (246665745951 / 250000000000)) := by
  have h := reflection_log_7790_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7791_neg : (232007121 / 1000000000) ≤ -Real.log (250000000000 / 315282177557) ∧
    -Real.log (250000000000 / 315282177557) ≤ (116003561 / 500000000) := by
  have h := checkLog_sound (w := (65282177557 / 565282177557)) (n := 12)
    (lo := (232007121 / 1000000000)) (hi := (116003561 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((315282177557 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(315282177557 / 250000000000) = 1/(250000000000 / 315282177557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7791 : Bounds (232007121 / 1000000000) (116003561 / 500000000) (Real.log (315282177557 / 250000000000)) := by
  have h := reflection_log_7791_neg
  have he : Real.log (315282177557 / 250000000000) = -Real.log (250000000000 / 315282177557) := by
    rw [show ((315282177557 / 250000000000) : ℝ) = ((250000000000 / 315282177557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7792_neg : (232990289 / 1000000000) ≤ -Real.log (25000000000 / 31559230523) ∧
    -Real.log (25000000000 / 31559230523) ≤ (23299029 / 100000000) := by
  have h := checkLog_sound (w := (6559230523 / 56559230523)) (n := 12)
    (lo := (232990289 / 1000000000)) (hi := (23299029 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31559230523 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31559230523 / 25000000000) = 1/(25000000000 / 31559230523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7792 : Bounds (232990289 / 1000000000) (23299029 / 100000000) (Real.log (31559230523 / 25000000000)) := by
  have h := reflection_log_7792_neg
  have he : Real.log (31559230523 / 25000000000) = -Real.log (25000000000 / 31559230523) := by
    rw [show ((31559230523 / 25000000000) : ℝ) = ((25000000000 / 31559230523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7793_neg : (58283467 / 125000000) ≤ -Real.log (500000000000 / 797016861219) ∧
    -Real.log (500000000000 / 797016861219) ≤ (466267737 / 1000000000) := by
  have h := checkLog_sound (w := (297016861219 / 1297016861219)) (n := 12)
    (lo := (58283467 / 125000000)) (hi := (466267737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((797016861219 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(797016861219 / 500000000000) = 1/(500000000000 / 797016861219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7793 : Bounds (58283467 / 125000000) (466267737 / 1000000000) (Real.log (797016861219 / 500000000000)) := by
  have h := reflection_log_7793_neg
  have he : Real.log (797016861219 / 500000000000) = -Real.log (500000000000 / 797016861219) := by
    rw [show ((797016861219 / 500000000000) : ℝ) = ((500000000000 / 797016861219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7794_neg : (233661603 / 500000000) ≤ -Real.log (25000000000 / 39892926671) ∧
    -Real.log (25000000000 / 39892926671) ≤ (467323207 / 1000000000) := by
  have h := checkLog_sound (w := (14892926671 / 64892926671)) (n := 12)
    (lo := (233661603 / 500000000)) (hi := (467323207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39892926671 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39892926671 / 25000000000) = 1/(25000000000 / 39892926671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7794 : Bounds (233661603 / 500000000) (467323207 / 1000000000) (Real.log (39892926671 / 25000000000)) := by
  have h := reflection_log_7794_neg
  have he : Real.log (39892926671 / 25000000000) = -Real.log (25000000000 / 39892926671) := by
    rw [show ((39892926671 / 25000000000) : ℝ) = ((25000000000 / 39892926671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7795_neg : (207014169 / 1000000000) ≤ -Real.log (100 / 123) ∧
    -Real.log (100 / 123) ≤ (20701417 / 100000000) := by
  have h := checkLog_sound (w := (23 / 223)) (n := 12)
    (lo := (207014169 / 1000000000)) (hi := (20701417 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123 / 100) = 1/(100 / 123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7795 : Bounds (207014169 / 1000000000) (20701417 / 100000000) (Real.log (123 / 100)) := by
  have h := reflection_log_7795_neg
  have he : Real.log (123 / 100) = -Real.log (100 / 123) := by
    rw [show ((123 / 100) : ℝ) = ((100 / 123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7796_neg : (65341191 / 250000000) ≤ -Real.log (77 / 100) ∧
    -Real.log (77 / 100) ≤ (52272953 / 200000000) := by
  have h := checkLog_sound (w := (23 / 177)) (n := 12)
    (lo := (65341191 / 250000000)) (hi := (52272953 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 77) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 77) = 1/(77 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7796 : Bounds (-52272953 / 200000000) (-65341191 / 250000000) (Real.log (77 / 100)) := by
  have h := reflection_log_7796_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7797_neg : (229973 / 1000000000) ≤ -Real.log (100000 / 100023) ∧
    -Real.log (100000 / 100023) ≤ (114987 / 500000000) := by
  have h := checkLog_sound (w := (23 / 200023)) (n := 12)
    (lo := (229973 / 1000000000)) (hi := (114987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100023 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100023 / 100000) = 1/(100000 / 100023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7797 : Bounds (229973 / 1000000000) (114987 / 500000000) (Real.log (100023 / 100000)) := by
  have h := reflection_log_7797_neg
  have he : Real.log (100023 / 100000) = -Real.log (100000 / 100023) := by
    rw [show ((100023 / 100000) : ℝ) = ((100000 / 100023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7798_neg : (115013 / 500000000) ≤ -Real.log (99977 / 100000) ∧
    -Real.log (99977 / 100000) ≤ (230027 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 199977)) (n := 12)
    (lo := (115013 / 500000000)) (hi := (230027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99977) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99977) = 1/(99977 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7798 : Bounds (-230027 / 1000000000) (-115013 / 500000000) (Real.log (99977 / 100000)) := by
  have h := reflection_log_7798_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7799_neg : (2190411 / 20000000) ≤ -Real.log (1000000 / 1115743) ∧
    -Real.log (1000000 / 1115743) ≤ (109520551 / 1000000000) := by
  have h := checkLog_sound (w := (115743 / 2115743)) (n := 12)
    (lo := (2190411 / 20000000)) (hi := (109520551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1115743 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1115743 / 1000000) = 1/(1000000 / 1115743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7799 : Bounds (2190411 / 20000000) (109520551 / 1000000000) (Real.log (1115743 / 1000000)) := by
  have h := reflection_log_7799_neg
  have he : Real.log (1115743 / 1000000) = -Real.log (1000000 / 1115743) := by
    rw [show ((1115743 / 1000000) : ℝ) = ((1000000 / 1115743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7800_neg : (61503767 / 500000000) ≤ -Real.log (884257 / 1000000) ∧
    -Real.log (884257 / 1000000) ≤ (24601507 / 200000000) := by
  have h := checkLog_sound (w := (115743 / 1884257)) (n := 12)
    (lo := (61503767 / 500000000)) (hi := (24601507 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 884257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 884257) = 1/(884257 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7800 : Bounds (-24601507 / 200000000) (-61503767 / 500000000) (Real.log (884257 / 1000000)) := by
  have h := reflection_log_7800_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7801_neg : (2748901 / 25000000) ≤ -Real.log (1000000 / 1116229) ∧
    -Real.log (1000000 / 1116229) ≤ (109956041 / 1000000000) := by
  have h := checkLog_sound (w := (116229 / 2116229)) (n := 12)
    (lo := (2748901 / 25000000)) (hi := (109956041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1116229 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1116229 / 1000000) = 1/(1000000 / 1116229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7801 : Bounds (2748901 / 25000000) (109956041 / 1000000000) (Real.log (1116229 / 1000000)) := by
  have h := reflection_log_7801_neg
  have he : Real.log (1116229 / 1000000) = -Real.log (1000000 / 1116229) := by
    rw [show ((1116229 / 1000000) : ℝ) = ((1000000 / 1116229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7802_neg : (123557299 / 1000000000) ≤ -Real.log (883771 / 1000000) ∧
    -Real.log (883771 / 1000000) ≤ (1235573 / 10000000) := by
  have h := checkLog_sound (w := (116229 / 1883771)) (n := 12)
    (lo := (123557299 / 1000000000)) (hi := (1235573 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 883771) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 883771) = 1/(883771 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7802 : Bounds (-1235573 / 10000000) (-123557299 / 1000000000) (Real.log (883771 / 1000000)) := by
  have h := reflection_log_7802_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7803_neg : (13601259 / 1000000000) ≤ -Real.log (986490819559 / 1000000000000) ∧
    -Real.log (986490819559 / 1000000000000) ≤ (680063 / 50000000) := by
  have h := checkLog_sound (w := (13509180441 / 1986490819559)) (n := 12)
    (lo := (13601259 / 1000000000)) (hi := (680063 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986490819559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986490819559) = 1/(986490819559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7803 : Bounds (-680063 / 50000000) (-13601259 / 1000000000) (Real.log (986490819559 / 1000000000000)) := by
  have h := reflection_log_7803_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7804_neg : (13486983 / 1000000000) ≤ -Real.log (986603557951 / 1000000000000) ∧
    -Real.log (986603557951 / 1000000000000) ≤ (1685873 / 125000000) := by
  have h := checkLog_sound (w := (13396442049 / 1986603557951)) (n := 12)
    (lo := (13486983 / 1000000000)) (hi := (1685873 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 986603557951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 986603557951) = 1/(986603557951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7804 : Bounds (-1685873 / 125000000) (-13486983 / 1000000000) (Real.log (986603557951 / 1000000000000)) := by
  have h := reflection_log_7804_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7805_neg : (46505617 / 200000000) ≤ -Real.log (500000000000 / 630892941757) ∧
    -Real.log (500000000000 / 630892941757) ≤ (116264043 / 500000000) := by
  have h := checkLog_sound (w := (130892941757 / 1130892941757)) (n := 12)
    (lo := (46505617 / 200000000)) (hi := (116264043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630892941757 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(630892941757 / 500000000000) = 1/(500000000000 / 630892941757) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7805 : Bounds (46505617 / 200000000) (116264043 / 500000000) (Real.log (630892941757 / 500000000000)) := by
  have h := reflection_log_7805_neg
  have he : Real.log (630892941757 / 500000000000) = -Real.log (500000000000 / 630892941757) := by
    rw [show ((630892941757 / 500000000000) : ℝ) = ((500000000000 / 630892941757) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7806_neg : (233513339 / 1000000000) ≤ -Real.log (12500000000 / 15787870953) ∧
    -Real.log (12500000000 / 15787870953) ≤ (11675667 / 50000000) := by
  have h := checkLog_sound (w := (3287870953 / 28287870953)) (n := 12)
    (lo := (233513339 / 1000000000)) (hi := (11675667 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15787870953 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15787870953 / 12500000000) = 1/(12500000000 / 15787870953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7806 : Bounds (233513339 / 1000000000) (11675667 / 50000000) (Real.log (15787870953 / 12500000000)) := by
  have h := reflection_log_7806_neg
  have he : Real.log (15787870953 / 12500000000) = -Real.log (12500000000 / 15787870953) := by
    rw [show ((15787870953 / 12500000000) : ℝ) = ((12500000000 / 15787870953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7807_neg : (233661603 / 500000000) ≤ -Real.log (500000000000 / 797858533419) ∧
    -Real.log (500000000000 / 797858533419) ≤ (467323207 / 1000000000) := by
  have h := checkLog_sound (w := (297858533419 / 1297858533419)) (n := 12)
    (lo := (233661603 / 500000000)) (hi := (467323207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((797858533419 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(797858533419 / 500000000000) = 1/(500000000000 / 797858533419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7807 : Bounds (233661603 / 500000000) (467323207 / 1000000000) (Real.log (797858533419 / 500000000000)) := by
  have h := reflection_log_7807_neg
  have he : Real.log (797858533419 / 500000000000) = -Real.log (500000000000 / 797858533419) := by
    rw [show ((797858533419 / 500000000000) : ℝ) = ((500000000000 / 797858533419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
