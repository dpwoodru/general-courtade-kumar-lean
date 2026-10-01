import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14464_neg : (11843837 / 3906250) ≤ -Real.log (500000000000 / 10369565217391) ∧
    -Real.log (500000000000 / 10369565217391) ≤ (3032022277 / 1000000000) := by
  have h := checkLog_sound (w := (2369565217391 / 18369565217391)) (n := 12)
    (lo := (16214597 / 62500000)) (hi := (259433553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10369565217391 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(10369565217391 / 8000000000000) = 1/(500000000000 / 10369565217391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14464 : Bounds (11843837 / 3906250) (3032022277 / 1000000000) (Real.log (10369565217391 / 500000000000)) := by
  have h := reflection_log_14464_neg
  have he : Real.log (10369565217391 / 500000000000) = -Real.log (500000000000 / 10369565217391) := by
    rw [show ((10369565217391 / 500000000000) : ℝ) = ((500000000000 / 10369565217391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14465_neg : (766686393 / 250000000) ≤ -Real.log (25000000000 / 536797752809) ∧
    -Real.log (25000000000 / 536797752809) ≤ (3066745577 / 1000000000) := by
  have h := checkLog_sound (w := (136797752809 / 936797752809)) (n := 12)
    (lo := (73539213 / 250000000)) (hi := (294156853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((536797752809 / 400000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(536797752809 / 400000000000) = 1/(25000000000 / 536797752809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14465 : Bounds (766686393 / 250000000) (3066745577 / 1000000000) (Real.log (536797752809 / 25000000000)) := by
  have h := reflection_log_14465_neg
  have he : Real.log (536797752809 / 25000000000) = -Real.log (25000000000 / 536797752809) := by
    rw [show ((536797752809 / 25000000000) : ℝ) = ((25000000000 / 536797752809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14466_neg : (649195293 / 1000000000) ≤ -Real.log (500 / 957) ∧
    -Real.log (500 / 957) ≤ (324597647 / 500000000) := by
  have h := checkLog_sound (w := (457 / 1457)) (n := 12)
    (lo := (649195293 / 1000000000)) (hi := (324597647 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((957 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(957 / 500) = 1/(500 / 957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14466 : Bounds (649195293 / 1000000000) (324597647 / 500000000) (Real.log (957 / 500)) := by
  have h := reflection_log_14466_neg
  have he : Real.log (957 / 500) = -Real.log (500 / 957) := by
    rw [show ((957 / 500) : ℝ) = ((500 / 957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14467_neg : (2453407981 / 1000000000) ≤ -Real.log (43 / 500) ∧
    -Real.log (43 / 500) ≤ (490681597 / 200000000) := by
  have h := checkLog_sound (w := (39 / 211)) (n := 12)
    (lo := (373966441 / 1000000000)) (hi := (186983221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 86) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 86) = 1/(43 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14467 : Bounds (-490681597 / 200000000) (-2453407981 / 1000000000) (Real.log (43 / 500)) := by
  have h := reflection_log_14467_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14468_neg : (456791 / 500000000) ≤ -Real.log (500000 / 500457) ∧
    -Real.log (500000 / 500457) ≤ (913583 / 1000000000) := by
  have h := checkLog_sound (w := (457 / 1000457)) (n := 12)
    (lo := (456791 / 500000000)) (hi := (913583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500457 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500457 / 500000) = 1/(500000 / 500457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14468 : Bounds (456791 / 500000000) (913583 / 1000000000) (Real.log (500457 / 500000)) := by
  have h := reflection_log_14468_neg
  have he : Real.log (500457 / 500000) = -Real.log (500000 / 500457) := by
    rw [show ((500457 / 500000) : ℝ) = ((500000 / 500457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14469_neg : (914417 / 1000000000) ≤ -Real.log (499543 / 500000) ∧
    -Real.log (499543 / 500000) ≤ (457209 / 500000000) := by
  have h := checkLog_sound (w := (457 / 999543)) (n := 12)
    (lo := (914417 / 1000000000)) (hi := (457209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499543) = 1/(499543 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14469 : Bounds (-457209 / 500000000) (-914417 / 1000000000) (Real.log (499543 / 500000)) := by
  have h := reflection_log_14469_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14470_neg : (440001147 / 1000000000) ≤ -Real.log (1000000 / 1552709) ∧
    -Real.log (1000000 / 1552709) ≤ (110000287 / 250000000) := by
  have h := checkLog_sound (w := (552709 / 2552709)) (n := 12)
    (lo := (440001147 / 1000000000)) (hi := (110000287 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1552709 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1552709 / 1000000) = 1/(1000000 / 1552709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14470 : Bounds (440001147 / 1000000000) (110000287 / 250000000) (Real.log (1552709 / 1000000)) := by
  have h := reflection_log_14470_neg
  have he : Real.log (1552709 / 1000000) = -Real.log (1000000 / 1552709) := by
    rw [show ((1552709 / 1000000) : ℝ) = ((1000000 / 1552709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14471_neg : (25142059 / 31250000) ≤ -Real.log (447291 / 1000000) ∧
    -Real.log (447291 / 1000000) ≤ (80454589 / 100000000) := by
  have h := checkLog_sound (w := (52709 / 947291)) (n := 12)
    (lo := (27849677 / 250000000)) (hi := (111398709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 447291) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 447291) = 1/(447291 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14471 : Bounds (-80454589 / 100000000) (-25142059 / 31250000) (Real.log (447291 / 1000000)) := by
  have h := reflection_log_14471_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14472_neg : (55285849 / 125000000) ≤ -Real.log (500000 / 778131) ∧
    -Real.log (500000 / 778131) ≤ (442286793 / 1000000000) := by
  have h := checkLog_sound (w := (278131 / 1278131)) (n := 12)
    (lo := (55285849 / 125000000)) (hi := (442286793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((778131 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(778131 / 500000) = 1/(500000 / 778131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14472 : Bounds (55285849 / 125000000) (442286793 / 1000000000) (Real.log (778131 / 500000)) := by
  have h := reflection_log_14472_neg
  have he : Real.log (778131 / 500000) = -Real.log (500000 / 778131) := by
    rw [show ((778131 / 500000) : ℝ) = ((500000 / 778131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14473_neg : (40626049 / 50000000) ≤ -Real.log (221869 / 500000) ∧
    -Real.log (221869 / 500000) ≤ (406260491 / 500000000) := by
  have h := checkLog_sound (w := (28131 / 471869)) (n := 12)
    (lo := (596869 / 5000000)) (hi := (119373801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 221869) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 221869) = 1/(221869 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14473 : Bounds (-406260491 / 500000000) (-40626049 / 50000000) (Real.log (221869 / 500000)) := by
  have h := reflection_log_14473_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14474_neg : (92558547 / 250000000) ≤ -Real.log (172643146839 / 250000000000) ∧
    -Real.log (172643146839 / 250000000000) ≤ (370234189 / 1000000000) := by
  have h := checkLog_sound (w := (77356853161 / 422643146839)) (n := 12)
    (lo := (92558547 / 250000000)) (hi := (370234189 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 172643146839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 172643146839) = 1/(172643146839 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14474 : Bounds (-370234189 / 1000000000) (-92558547 / 250000000) (Real.log (172643146839 / 250000000000)) := by
  have h := reflection_log_14474_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14475_neg : (182272371 / 500000000) ≤ -Real.log (694512761319 / 1000000000000) ∧
    -Real.log (694512761319 / 1000000000000) ≤ (364544743 / 1000000000) := by
  have h := checkLog_sound (w := (305487238681 / 1694512761319)) (n := 12)
    (lo := (182272371 / 500000000)) (hi := (364544743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 694512761319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 694512761319) = 1/(694512761319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14475 : Bounds (-364544743 / 1000000000) (-182272371 / 500000000) (Real.log (694512761319 / 1000000000000)) := by
  have h := reflection_log_14475_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14476_neg : (311136759 / 250000000) ≤ -Real.log (250000000000 / 867840510987) ∧
    -Real.log (250000000000 / 867840510987) ≤ (622273519 / 500000000) := by
  have h := checkLog_sound (w := (367840510987 / 1367840510987)) (n := 12)
    (lo := (34462491 / 62500000)) (hi := (551399857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((867840510987 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(867840510987 / 500000000000) = 1/(250000000000 / 867840510987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14476 : Bounds (311136759 / 250000000) (622273519 / 500000000) (Real.log (867840510987 / 250000000000)) := by
  have h := reflection_log_14476_neg
  have he : Real.log (867840510987 / 250000000000) = -Real.log (250000000000 / 867840510987) := by
    rw [show ((867840510987 / 250000000000) : ℝ) = ((250000000000 / 867840510987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14477_neg : (313701943 / 250000000) ≤ -Real.log (500000000000 / 1753582068699) ∧
    -Real.log (500000000000 / 1753582068699) ≤ (627403887 / 500000000) := by
  have h := checkLog_sound (w := (753582068699 / 2753582068699)) (n := 12)
    (lo := (35103787 / 62500000)) (hi := (561660593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1753582068699 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1753582068699 / 1000000000000) = 1/(500000000000 / 1753582068699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14477 : Bounds (313701943 / 250000000) (627403887 / 500000000) (Real.log (1753582068699 / 500000000000)) := by
  have h := reflection_log_14477_neg
  have he : Real.log (1753582068699 / 500000000000) = -Real.log (500000000000 / 1753582068699) := by
    rw [show ((1753582068699 / 500000000000) : ℝ) = ((500000000000 / 1753582068699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14478_neg : (766686393 / 250000000) ≤ -Real.log (500000000000 / 10735955056179) ∧
    -Real.log (500000000000 / 10735955056179) ≤ (3066745577 / 1000000000) := by
  have h := checkLog_sound (w := (2735955056179 / 18735955056179)) (n := 12)
    (lo := (73539213 / 250000000)) (hi := (294156853 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10735955056179 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(10735955056179 / 8000000000000) = 1/(500000000000 / 10735955056179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14478 : Bounds (766686393 / 250000000) (3066745577 / 1000000000) (Real.log (10735955056179 / 500000000000)) := by
  have h := reflection_log_14478_neg
  have he : Real.log (10735955056179 / 500000000000) = -Real.log (500000000000 / 10735955056179) := by
    rw [show ((10735955056179 / 500000000000) : ℝ) = ((500000000000 / 10735955056179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14479_neg : (3102603273 / 1000000000) ≤ -Real.log (100000000000 / 2225581395349) ∧
    -Real.log (100000000000 / 2225581395349) ≤ (1551301639 / 500000000) := by
  have h := checkLog_sound (w := (625581395349 / 3825581395349)) (n := 12)
    (lo := (330014553 / 1000000000)) (hi := (165007277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2225581395349 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2225581395349 / 1600000000000) = 1/(100000000000 / 2225581395349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14479 : Bounds (3102603273 / 1000000000) (1551301639 / 500000000) (Real.log (2225581395349 / 100000000000)) := by
  have h := reflection_log_14479_neg
  have he : Real.log (2225581395349 / 100000000000) = -Real.log (100000000000 / 2225581395349) := by
    rw [show ((2225581395349 / 100000000000) : ℝ) = ((100000000000 / 2225581395349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14480_neg : (81345183 / 125000000) ≤ -Real.log (1000 / 1917) ∧
    -Real.log (1000 / 1917) ≤ (130152293 / 200000000) := by
  have h := checkLog_sound (w := (917 / 2917)) (n := 12)
    (lo := (81345183 / 125000000)) (hi := (130152293 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1917 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1917 / 1000) = 1/(1000 / 1917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14480 : Bounds (81345183 / 125000000) (130152293 / 200000000) (Real.log (1917 / 1000)) := by
  have h := reflection_log_14480_neg
  have he : Real.log (1917 / 1000) = -Real.log (1000 / 1917) := by
    rw [show ((1917 / 1000) : ℝ) = ((1000 / 1917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14481_neg : (2488914669 / 1000000000) ≤ -Real.log (83 / 1000) ∧
    -Real.log (83 / 1000) ≤ (2488914673 / 1000000000) := by
  have h := checkLog_sound (w := (21 / 104)) (n := 12)
    (lo := (409473129 / 1000000000)) (hi := (40947313 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 83) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 83) = 1/(83 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14481 : Bounds (-2488914673 / 1000000000) (-2488914669 / 1000000000) (Real.log (83 / 1000)) := by
  have h := reflection_log_14481_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14482_neg : (916579 / 1000000000) ≤ -Real.log (1000000 / 1000917) ∧
    -Real.log (1000000 / 1000917) ≤ (45829 / 50000000) := by
  have h := checkLog_sound (w := (917 / 2000917)) (n := 12)
    (lo := (916579 / 1000000000)) (hi := (45829 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000917 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000917 / 1000000) = 1/(1000000 / 1000917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14482 : Bounds (916579 / 1000000000) (45829 / 50000000) (Real.log (1000917 / 1000000)) := by
  have h := reflection_log_14482_neg
  have he : Real.log (1000917 / 1000000) = -Real.log (1000000 / 1000917) := by
    rw [show ((1000917 / 1000000) : ℝ) = ((1000000 / 1000917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14483_neg : (45871 / 50000000) ≤ -Real.log (999083 / 1000000) ∧
    -Real.log (999083 / 1000000) ≤ (917421 / 1000000000) := by
  have h := checkLog_sound (w := (917 / 1999083)) (n := 12)
    (lo := (45871 / 50000000)) (hi := (917421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999083) = 1/(999083 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14483 : Bounds (-917421 / 1000000000) (-45871 / 50000000) (Real.log (999083 / 1000000)) := by
  have h := reflection_log_14483_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14484_neg : (220927447 / 500000000) ≤ -Real.log (100000 / 155559) ∧
    -Real.log (100000 / 155559) ≤ (88370979 / 200000000) := by
  have h := checkLog_sound (w := (55559 / 255559)) (n := 12)
    (lo := (220927447 / 500000000)) (hi := (88370979 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155559 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155559 / 100000) = 1/(100000 / 155559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14484 : Bounds (220927447 / 500000000) (88370979 / 200000000) (Real.log (155559 / 100000)) := by
  have h := reflection_log_14484_neg
  have he : Real.log (155559 / 100000) = -Real.log (100000 / 155559) := by
    rw [show ((155559 / 100000) : ℝ) = ((100000 / 155559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14485_neg : (405503859 / 500000000) ≤ -Real.log (44441 / 100000) ∧
    -Real.log (44441 / 100000) ≤ (20275193 / 25000000) := by
  have h := checkLog_sound (w := (5559 / 94441)) (n := 12)
    (lo := (58930269 / 500000000)) (hi := (117860539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 44441) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 44441) = 1/(44441 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14485 : Bounds (-20275193 / 25000000) (-405503859 / 500000000) (Real.log (44441 / 100000)) := by
  have h := reflection_log_14485_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14486_neg : (222075531 / 500000000) ≤ -Real.log (500000 / 779583) ∧
    -Real.log (500000 / 779583) ≤ (444151063 / 1000000000) := by
  have h := checkLog_sound (w := (279583 / 1279583)) (n := 12)
    (lo := (222075531 / 500000000)) (hi := (444151063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((779583 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(779583 / 500000) = 1/(500000 / 779583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14486 : Bounds (222075531 / 500000000) (444151063 / 1000000000) (Real.log (779583 / 500000)) := by
  have h := reflection_log_14486_neg
  have he : Real.log (779583 / 500000) = -Real.log (500000 / 779583) := by
    rw [show ((779583 / 500000) : ℝ) = ((500000 / 779583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14487_neg : (819086891 / 1000000000) ≤ -Real.log (220417 / 500000) ∧
    -Real.log (220417 / 500000) ≤ (819086893 / 1000000000) := by
  have h := checkLog_sound (w := (29583 / 470417)) (n := 12)
    (lo := (125939711 / 1000000000)) (hi := (245976 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 220417) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 220417) = 1/(220417 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14487 : Bounds (-819086893 / 1000000000) (-819086891 / 1000000000) (Real.log (220417 / 500000)) := by
  have h := reflection_log_14487_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14488_neg : (93733957 / 250000000) ≤ -Real.log (171833346111 / 250000000000) ∧
    -Real.log (171833346111 / 250000000000) ≤ (374935829 / 1000000000) := by
  have h := checkLog_sound (w := (78166653889 / 421833346111)) (n := 12)
    (lo := (93733957 / 250000000)) (hi := (374935829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 171833346111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 171833346111) = 1/(171833346111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14488 : Bounds (-374935829 / 1000000000) (-93733957 / 250000000) (Real.log (171833346111 / 250000000000)) := by
  have h := reflection_log_14488_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14489_neg : (46144103 / 125000000) ≤ -Real.log (6913197519 / 10000000000) ∧
    -Real.log (6913197519 / 10000000000) ≤ (14766113 / 40000000) := by
  have h := checkLog_sound (w := (3086802481 / 16913197519)) (n := 12)
    (lo := (46144103 / 125000000)) (hi := (14766113 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 6913197519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 6913197519) = 1/(6913197519 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14489 : Bounds (-14766113 / 40000000) (-46144103 / 125000000) (Real.log (6913197519 / 10000000000)) := by
  have h := reflection_log_14489_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14490_neg : (1252862613 / 1000000000) ≤ -Real.log (100000000000 / 350034877703) ∧
    -Real.log (100000000000 / 350034877703) ≤ (250572523 / 200000000) := by
  have h := checkLog_sound (w := (150034877703 / 550034877703)) (n := 12)
    (lo := (559715433 / 1000000000)) (hi := (279857717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((350034877703 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(350034877703 / 200000000000) = 1/(100000000000 / 350034877703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14490 : Bounds (1252862613 / 1000000000) (250572523 / 200000000) (Real.log (350034877703 / 100000000000)) := by
  have h := reflection_log_14490_neg
  have he : Real.log (350034877703 / 100000000000) = -Real.log (100000000000 / 350034877703) := by
    rw [show ((350034877703 / 100000000000) : ℝ) = ((100000000000 / 350034877703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14491_neg : (1263237953 / 1000000000) ≤ -Real.log (500000000000 / 1768427571377) ∧
    -Real.log (500000000000 / 1768427571377) ≤ (252647591 / 200000000) := by
  have h := checkLog_sound (w := (768427571377 / 2768427571377)) (n := 12)
    (lo := (570090773 / 1000000000)) (hi := (285045387 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1768427571377 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1768427571377 / 1000000000000) = 1/(500000000000 / 1768427571377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14491 : Bounds (1263237953 / 1000000000) (252647591 / 200000000) (Real.log (1768427571377 / 500000000000)) := by
  have h := reflection_log_14491_neg
  have he : Real.log (1768427571377 / 500000000000) = -Real.log (500000000000 / 1768427571377) := by
    rw [show ((1768427571377 / 500000000000) : ℝ) = ((500000000000 / 1768427571377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14492_neg : (3102603273 / 1000000000) ≤ -Real.log (62500000000 / 1390988372093) ∧
    -Real.log (62500000000 / 1390988372093) ≤ (1551301639 / 500000000) := by
  have h := checkLog_sound (w := (390988372093 / 2390988372093)) (n := 12)
    (lo := (330014553 / 1000000000)) (hi := (165007277 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1390988372093 / 1000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1390988372093 / 1000000000000) = 1/(62500000000 / 1390988372093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14492 : Bounds (3102603273 / 1000000000) (1551301639 / 500000000) (Real.log (1390988372093 / 62500000000)) := by
  have h := reflection_log_14492_neg
  have he : Real.log (1390988372093 / 62500000000) = -Real.log (62500000000 / 1390988372093) := by
    rw [show ((1390988372093 / 62500000000) : ℝ) = ((62500000000 / 1390988372093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14493_neg : (3139676133 / 1000000000) ≤ -Real.log (100000000000 / 2309638554217) ∧
    -Real.log (100000000000 / 2309638554217) ≤ (1569838069 / 500000000) := by
  have h := checkLog_sound (w := (709638554217 / 3909638554217)) (n := 12)
    (lo := (367087413 / 1000000000)) (hi := (183543707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2309638554217 / 1600000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2309638554217 / 1600000000000) = 1/(100000000000 / 2309638554217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14493 : Bounds (3139676133 / 1000000000) (1569838069 / 500000000) (Real.log (2309638554217 / 100000000000)) := by
  have h := reflection_log_14493_neg
  have he : Real.log (2309638554217 / 100000000000) = -Real.log (100000000000 / 2309638554217) := by
    rw [show ((2309638554217 / 100000000000) : ℝ) = ((100000000000 / 2309638554217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14494_neg : (326162593 / 500000000) ≤ -Real.log (25 / 48) ∧
    -Real.log (25 / 48) ≤ (652325187 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 73)) (n := 12)
    (lo := (326162593 / 500000000)) (hi := (652325187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48 / 25) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(48 / 25) = 1/(25 / 48) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14494 : Bounds (326162593 / 500000000) (652325187 / 1000000000) (Real.log (48 / 25)) := by
  have h := reflection_log_14494_neg
  have he : Real.log (48 / 25) = -Real.log (25 / 48) := by
    rw [show ((48 / 25) : ℝ) = ((25 / 48) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14495_neg : (1262864321 / 500000000) ≤ -Real.log (2 / 25) ∧
    -Real.log (2 / 25) ≤ (1262864323 / 500000000) := by
  have h := checkLog_sound (w := (9 / 41)) (n := 12)
    (lo := (223143551 / 500000000)) (hi := (446287103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 16) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25 / 16) = 1/(2 / 25) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14495 : Bounds (-1262864323 / 500000000) (-1262864321 / 500000000) (Real.log (2 / 25)) := by
  have h := reflection_log_14495_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14496_neg : (919577 / 1000000000) ≤ -Real.log (25000 / 25023) ∧
    -Real.log (25000 / 25023) ≤ (459789 / 500000000) := by
  have h := checkLog_sound (w := (23 / 50023)) (n := 12)
    (lo := (919577 / 1000000000)) (hi := (459789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25023 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25023 / 25000) = 1/(25000 / 25023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14496 : Bounds (919577 / 1000000000) (459789 / 500000000) (Real.log (25023 / 25000)) := by
  have h := reflection_log_14496_neg
  have he : Real.log (25023 / 25000) = -Real.log (25000 / 25023) := by
    rw [show ((25023 / 25000) : ℝ) = ((25000 / 25023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14497_neg : (920423 / 1000000000) ≤ -Real.log (24977 / 25000) ∧
    -Real.log (24977 / 25000) ≤ (115053 / 125000000) := by
  have h := checkLog_sound (w := (23 / 49977)) (n := 12)
    (lo := (920423 / 1000000000)) (hi := (115053 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 24977) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 24977) = 1/(24977 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14497 : Bounds (-115053 / 125000000) (-920423 / 1000000000) (Real.log (24977 / 25000)) := by
  have h := reflection_log_14497_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14498_neg : (110930153 / 250000000) ≤ -Real.log (200000 / 311699) ∧
    -Real.log (200000 / 311699) ≤ (443720613 / 1000000000) := by
  have h := checkLog_sound (w := (111699 / 511699)) (n := 12)
    (lo := (110930153 / 250000000)) (hi := (443720613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311699 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311699 / 200000) = 1/(200000 / 311699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14498 : Bounds (110930153 / 250000000) (443720613 / 1000000000) (Real.log (311699 / 200000)) := by
  have h := reflection_log_14498_neg
  have he : Real.log (311699 / 200000) = -Real.log (200000 / 311699) := by
    rw [show ((311699 / 200000) : ℝ) = ((200000 / 311699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14499_neg : (817565933 / 1000000000) ≤ -Real.log (88301 / 200000) ∧
    -Real.log (88301 / 200000) ≤ (163513187 / 200000000) := by
  have h := checkLog_sound (w := (11699 / 188301)) (n := 12)
    (lo := (124418753 / 1000000000)) (hi := (62209377 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 88301) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 88301) = 1/(88301 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14499 : Bounds (-163513187 / 200000000) (-817565933 / 1000000000) (Real.log (88301 / 200000)) := by
  have h := reflection_log_14499_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14500_neg : (446028509 / 1000000000) ≤ -Real.log (62500 / 97631) ∧
    -Real.log (62500 / 97631) ≤ (44602851 / 100000000) := by
  have h := checkLog_sound (w := (35131 / 160131)) (n := 12)
    (lo := (446028509 / 1000000000)) (hi := (44602851 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97631 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97631 / 62500) = 1/(62500 / 97631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14500 : Bounds (446028509 / 1000000000) (44602851 / 100000000) (Real.log (97631 / 62500)) := by
  have h := reflection_log_14500_neg
  have he : Real.log (97631 / 62500) = -Real.log (62500 / 97631) := by
    rw [show ((97631 / 62500) : ℝ) = ((62500 / 97631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14501_neg : (82575557 / 100000000) ≤ -Real.log (27369 / 62500) ∧
    -Real.log (27369 / 62500) ≤ (206438893 / 250000000) := by
  have h := checkLog_sound (w := (3881 / 58619)) (n := 12)
    (lo := (13260839 / 100000000)) (hi := (132608391 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27369) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 27369) = 1/(27369 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14501 : Bounds (-206438893 / 250000000) (-82575557 / 100000000) (Real.log (27369 / 62500)) := by
  have h := reflection_log_14501_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14502_neg : (379727061 / 1000000000) ≤ -Real.log (2672062839 / 3906250000) ∧
    -Real.log (2672062839 / 3906250000) ≤ (189863531 / 500000000) := by
  have h := checkLog_sound (w := (1234187161 / 6578312839)) (n := 12)
    (lo := (379727061 / 1000000000)) (hi := (189863531 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 2672062839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 2672062839) = 1/(2672062839 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14502 : Bounds (-189863531 / 500000000) (-379727061 / 1000000000) (Real.log (2672062839 / 3906250000)) := by
  have h := reflection_log_14502_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14503_neg : (373845321 / 1000000000) ≤ -Real.log (27523333399 / 40000000000) ∧
    -Real.log (27523333399 / 40000000000) ≤ (186922661 / 500000000) := by
  have h := checkLog_sound (w := (12476666601 / 67523333399)) (n := 12)
    (lo := (373845321 / 1000000000)) (hi := (186922661 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 27523333399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 27523333399) = 1/(27523333399 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14503 : Bounds (-186922661 / 500000000) (-373845321 / 1000000000) (Real.log (27523333399 / 40000000000)) := by
  have h := reflection_log_14503_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14504_neg : (252257309 / 200000000) ≤ -Real.log (500000000000 / 1764980011551) ∧
    -Real.log (500000000000 / 1764980011551) ≤ (1261286547 / 1000000000) := by
  have h := checkLog_sound (w := (764980011551 / 2764980011551)) (n := 12)
    (lo := (113627873 / 200000000)) (hi := (284069683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1764980011551 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1764980011551 / 1000000000000) = 1/(500000000000 / 1764980011551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14504 : Bounds (252257309 / 200000000) (1261286547 / 1000000000) (Real.log (1764980011551 / 500000000000)) := by
  have h := reflection_log_14504_neg
  have he : Real.log (1764980011551 / 500000000000) = -Real.log (500000000000 / 1764980011551) := by
    rw [show ((1764980011551 / 500000000000) : ℝ) = ((500000000000 / 1764980011551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14505_neg : (1271784079 / 1000000000) ≤ -Real.log (250000000000 / 891802769557) ∧
    -Real.log (250000000000 / 891802769557) ≤ (1271784081 / 1000000000) := by
  have h := checkLog_sound (w := (391802769557 / 1391802769557)) (n := 12)
    (lo := (578636899 / 1000000000)) (hi := (5786369 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((891802769557 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(891802769557 / 500000000000) = 1/(250000000000 / 891802769557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14505 : Bounds (1271784079 / 1000000000) (1271784081 / 1000000000) (Real.log (891802769557 / 250000000000)) := by
  have h := reflection_log_14505_neg
  have he : Real.log (891802769557 / 250000000000) = -Real.log (250000000000 / 891802769557) := by
    rw [show ((891802769557 / 250000000000) : ℝ) = ((250000000000 / 891802769557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14506_neg : (3139676133 / 1000000000) ≤ -Real.log (125000000000 / 2887048192771) ∧
    -Real.log (125000000000 / 2887048192771) ≤ (1569838069 / 500000000) := by
  have h := checkLog_sound (w := (887048192771 / 4887048192771)) (n := 12)
    (lo := (367087413 / 1000000000)) (hi := (183543707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2887048192771 / 2000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(2887048192771 / 2000000000000) = 1/(125000000000 / 2887048192771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14506 : Bounds (3139676133 / 1000000000) (1569838069 / 500000000) (Real.log (2887048192771 / 125000000000)) := by
  have h := reflection_log_14506_neg
  have he : Real.log (2887048192771 / 125000000000) = -Real.log (125000000000 / 2887048192771) := by
    rw [show ((2887048192771 / 125000000000) : ℝ) = ((125000000000 / 2887048192771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14507_neg : (794513457 / 250000000) ≤ -Real.log (1 / 24) ∧
    -Real.log (1 / 24) ≤ (3178053833 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 5)) (n := 12)
    (lo := (101366277 / 250000000)) (hi := (405465109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3 / 2) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3 / 2) = 1/(1 / 24) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14507 : Bounds (794513457 / 250000000) (3178053833 / 1000000000) (Real.log (24 / 1)) := by
  have h := reflection_log_14507_neg
  have he : Real.log (24 / 1) = -Real.log (1 / 24) := by
    rw [show ((24 / 1) : ℝ) = ((1 / 24) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14508_neg : (326943233 / 500000000) ≤ -Real.log (1000 / 1923) ∧
    -Real.log (1000 / 1923) ≤ (653886467 / 1000000000) := by
  have h := checkLog_sound (w := (923 / 2923)) (n := 12)
    (lo := (326943233 / 500000000)) (hi := (653886467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1923 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1923 / 1000) = 1/(1000 / 1923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14508 : Bounds (326943233 / 500000000) (653886467 / 1000000000) (Real.log (1923 / 1000)) := by
  have h := reflection_log_14508_neg
  have he : Real.log (1923 / 1000) = -Real.log (1000 / 1923) := by
    rw [show ((1923 / 1000) : ℝ) = ((1000 / 1923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14509_neg : (512789971 / 200000000) ≤ -Real.log (77 / 1000) ∧
    -Real.log (77 / 1000) ≤ (2563949859 / 1000000000) := by
  have h := checkLog_sound (w := (24 / 101)) (n := 12)
    (lo := (96901663 / 200000000)) (hi := (121127079 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 77) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 77) = 1/(77 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14509 : Bounds (-2563949859 / 1000000000) (-512789971 / 200000000) (Real.log (77 / 1000)) := by
  have h := reflection_log_14509_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14510_neg : (461287 / 500000000) ≤ -Real.log (1000000 / 1000923) ∧
    -Real.log (1000000 / 1000923) ≤ (36903 / 40000000) := by
  have h := checkLog_sound (w := (923 / 2000923)) (n := 12)
    (lo := (461287 / 500000000)) (hi := (36903 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000923 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000923 / 1000000) = 1/(1000000 / 1000923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14510 : Bounds (461287 / 500000000) (36903 / 40000000) (Real.log (1000923 / 1000000)) := by
  have h := reflection_log_14510_neg
  have he : Real.log (1000923 / 1000000) = -Real.log (1000000 / 1000923) := by
    rw [show ((1000923 / 1000000) : ℝ) = ((1000000 / 1000923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14511_neg : (461713 / 500000000) ≤ -Real.log (999077 / 1000000) ∧
    -Real.log (999077 / 1000000) ≤ (923427 / 1000000000) := by
  have h := checkLog_sound (w := (923 / 1999077)) (n := 12)
    (lo := (461713 / 500000000)) (hi := (923427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999077) = 1/(999077 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14511 : Bounds (-923427 / 1000000000) (-461713 / 500000000) (Real.log (999077 / 1000000)) := by
  have h := reflection_log_14511_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14512_neg : (222799753 / 500000000) ≤ -Real.log (500000 / 780713) ∧
    -Real.log (500000 / 780713) ≤ (445599507 / 1000000000) := by
  have h := checkLog_sound (w := (280713 / 1280713)) (n := 12)
    (lo := (222799753 / 500000000)) (hi := (445599507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((780713 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(780713 / 500000) = 1/(500000 / 780713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14512 : Bounds (222799753 / 500000000) (445599507 / 1000000000) (Real.log (780713 / 500000)) := by
  have h := reflection_log_14512_neg
  have he : Real.log (780713 / 500000) = -Real.log (500000 / 780713) := by
    rw [show ((780713 / 500000) : ℝ) = ((500000 / 780713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14513_neg : (824226723 / 1000000000) ≤ -Real.log (219287 / 500000) ∧
    -Real.log (219287 / 500000) ≤ (32969069 / 40000000) := by
  have h := checkLog_sound (w := (30713 / 469287)) (n := 12)
    (lo := (131079543 / 1000000000)) (hi := (16384943 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 219287) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 219287) = 1/(219287 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14513 : Bounds (-32969069 / 40000000) (-824226723 / 1000000000) (Real.log (219287 / 500000)) := by
  have h := reflection_log_14513_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14514_neg : (447919689 / 1000000000) ≤ -Real.log (1000000 / 1565053) ∧
    -Real.log (1000000 / 1565053) ≤ (44791969 / 100000000) := by
  have h := checkLog_sound (w := (565053 / 2565053)) (n := 12)
    (lo := (447919689 / 1000000000)) (hi := (44791969 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1565053 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1565053 / 1000000) = 1/(1000000 / 1565053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14514 : Bounds (447919689 / 1000000000) (44791969 / 100000000) (Real.log (1565053 / 1000000)) := by
  have h := reflection_log_14514_neg
  have he : Real.log (1565053 / 1000000) = -Real.log (1000000 / 1565053) := by
    rw [show ((1565053 / 1000000) : ℝ) = ((1000000 / 1565053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14515_neg : (832531093 / 1000000000) ≤ -Real.log (434947 / 1000000) ∧
    -Real.log (434947 / 1000000) ≤ (166506219 / 200000000) := by
  have h := checkLog_sound (w := (65053 / 934947)) (n := 12)
    (lo := (139383913 / 1000000000)) (hi := (69691957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 434947) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 434947) = 1/(434947 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14515 : Bounds (-166506219 / 200000000) (-832531093 / 1000000000) (Real.log (434947 / 1000000)) := by
  have h := reflection_log_14515_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14516_neg : (76922281 / 200000000) ≤ -Real.log (680715107191 / 1000000000000) ∧
    -Real.log (680715107191 / 1000000000000) ≤ (192305703 / 500000000) := by
  have h := checkLog_sound (w := (319284892809 / 1680715107191)) (n := 12)
    (lo := (76922281 / 200000000)) (hi := (192305703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 680715107191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 680715107191) = 1/(680715107191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14516 : Bounds (-192305703 / 500000000) (-76922281 / 200000000) (Real.log (680715107191 / 1000000000000)) := by
  have h := reflection_log_14516_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14517_neg : (378627217 / 1000000000) ≤ -Real.log (171200211631 / 250000000000) ∧
    -Real.log (171200211631 / 250000000000) ≤ (189313609 / 500000000) := by
  have h := checkLog_sound (w := (78799788369 / 421200211631)) (n := 12)
    (lo := (378627217 / 1000000000)) (hi := (189313609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 171200211631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 171200211631) = 1/(171200211631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14517 : Bounds (-189313609 / 500000000) (-378627217 / 1000000000) (Real.log (171200211631 / 250000000000)) := by
  have h := reflection_log_14517_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14518_neg : (126982623 / 100000000) ≤ -Real.log (100000000000 / 356023384879) ∧
    -Real.log (100000000000 / 356023384879) ≤ (158728279 / 125000000) := by
  have h := checkLog_sound (w := (156023384879 / 556023384879)) (n := 12)
    (lo := (11533581 / 20000000)) (hi := (576679051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((356023384879 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(356023384879 / 200000000000) = 1/(100000000000 / 356023384879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14518 : Bounds (126982623 / 100000000) (158728279 / 125000000) (Real.log (356023384879 / 100000000000)) := by
  have h := reflection_log_14518_neg
  have he : Real.log (356023384879 / 100000000000) = -Real.log (100000000000 / 356023384879) := by
    rw [show ((356023384879 / 100000000000) : ℝ) = ((100000000000 / 356023384879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14519_neg : (1280450783 / 1000000000) ≤ -Real.log (500000000000 / 1799130698683) ∧
    -Real.log (500000000000 / 1799130698683) ≤ (256090157 / 200000000) := by
  have h := checkLog_sound (w := (799130698683 / 2799130698683)) (n := 12)
    (lo := (587303603 / 1000000000)) (hi := (146825901 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1799130698683 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1799130698683 / 1000000000000) = 1/(500000000000 / 1799130698683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14519 : Bounds (1280450783 / 1000000000) (256090157 / 200000000) (Real.log (1799130698683 / 500000000000)) := by
  have h := reflection_log_14519_neg
  have he : Real.log (1799130698683 / 500000000000) = -Real.log (500000000000 / 1799130698683) := by
    rw [show ((1799130698683 / 500000000000) : ℝ) = ((500000000000 / 1799130698683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14520_neg : (3217836321 / 1000000000) ≤ -Real.log (500000000000 / 12487012987013) ∧
    -Real.log (500000000000 / 12487012987013) ≤ (1608918163 / 500000000) := by
  have h := checkLog_sound (w := (4487012987013 / 20487012987013)) (n := 12)
    (lo := (445247601 / 1000000000)) (hi := (222623801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12487012987013 / 8000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(12487012987013 / 8000000000000) = 1/(500000000000 / 12487012987013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14520 : Bounds (3217836321 / 1000000000) (1608918163 / 500000000) (Real.log (12487012987013 / 500000000000)) := by
  have h := reflection_log_14520_neg
  have he : Real.log (12487012987013 / 500000000000) = -Real.log (500000000000 / 12487012987013) := by
    rw [show ((12487012987013 / 500000000000) : ℝ) = ((500000000000 / 12487012987013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14521_neg : (655445313 / 1000000000) ≤ -Real.log (500 / 963) ∧
    -Real.log (500 / 963) ≤ (327722657 / 500000000) := by
  have h := checkLog_sound (w := (463 / 1463)) (n := 12)
    (lo := (655445313 / 1000000000)) (hi := (327722657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((963 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(963 / 500) = 1/(500 / 963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14521 : Bounds (655445313 / 1000000000) (327722657 / 500000000) (Real.log (963 / 500)) := by
  have h := reflection_log_14521_neg
  have he : Real.log (963 / 500) = -Real.log (500 / 963) := by
    rw [show ((963 / 500) : ℝ) = ((500 / 963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14522_neg : (325461273 / 125000000) ≤ -Real.log (37 / 500) ∧
    -Real.log (37 / 500) ≤ (650922547 / 250000000) := by
  have h := checkLog_sound (w := (51 / 199)) (n := 12)
    (lo := (131062161 / 250000000)) (hi := (104849729 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 74) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125 / 74) = 1/(37 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14522 : Bounds (-650922547 / 250000000) (-325461273 / 125000000) (Real.log (37 / 500)) := by
  have h := reflection_log_14522_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14523_neg : (925571 / 1000000000) ≤ -Real.log (500000 / 500463) ∧
    -Real.log (500000 / 500463) ≤ (231393 / 250000000) := by
  have h := checkLog_sound (w := (463 / 1000463)) (n := 12)
    (lo := (925571 / 1000000000)) (hi := (231393 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500463 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500463 / 500000) = 1/(500000 / 500463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14523 : Bounds (925571 / 1000000000) (231393 / 250000000) (Real.log (500463 / 500000)) := by
  have h := reflection_log_14523_neg
  have he : Real.log (500463 / 500000) = -Real.log (500000 / 500463) := by
    rw [show ((500463 / 500000) : ℝ) = ((500000 / 500463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14524_neg : (926429 / 1000000000) ≤ -Real.log (499537 / 500000) ∧
    -Real.log (499537 / 500000) ≤ (92643 / 100000000) := by
  have h := checkLog_sound (w := (463 / 999537)) (n := 12)
    (lo := (926429 / 1000000000)) (hi := (92643 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499537) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499537) = 1/(499537 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14524 : Bounds (-92643 / 100000000) (-926429 / 1000000000) (Real.log (499537 / 500000)) := by
  have h := reflection_log_14524_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14525_neg : (447491497 / 1000000000) ≤ -Real.log (1000000 / 1564383) ∧
    -Real.log (1000000 / 1564383) ≤ (223745749 / 500000000) := by
  have h := checkLog_sound (w := (564383 / 2564383)) (n := 12)
    (lo := (447491497 / 1000000000)) (hi := (223745749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1564383 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1564383 / 1000000) = 1/(1000000 / 1564383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14525 : Bounds (447491497 / 1000000000) (223745749 / 500000000) (Real.log (1564383 / 1000000)) := by
  have h := reflection_log_14525_neg
  have he : Real.log (1564383 / 1000000) = -Real.log (1000000 / 1564383) := by
    rw [show ((1564383 / 1000000) : ℝ) = ((1000000 / 1564383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14526_neg : (830991861 / 1000000000) ≤ -Real.log (435617 / 1000000) ∧
    -Real.log (435617 / 1000000) ≤ (830991863 / 1000000000) := by
  have h := checkLog_sound (w := (64383 / 935617)) (n := 12)
    (lo := (137844681 / 1000000000)) (hi := (68922341 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 435617) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 435617) = 1/(435617 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14526 : Bounds (-830991863 / 1000000000) (-830991861 / 1000000000) (Real.log (435617 / 1000000)) := by
  have h := reflection_log_14526_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14527_neg : (224912259 / 500000000) ≤ -Real.log (1000000 / 1568037) ∧
    -Real.log (1000000 / 1568037) ≤ (449824519 / 1000000000) := by
  have h := checkLog_sound (w := (568037 / 2568037)) (n := 12)
    (lo := (224912259 / 500000000)) (hi := (449824519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1568037 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1568037 / 1000000) = 1/(1000000 / 1568037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14527 : Bounds (224912259 / 500000000) (449824519 / 1000000000) (Real.log (1568037 / 1000000)) := by
  have h := reflection_log_14527_neg
  have he : Real.log (1568037 / 1000000) = -Real.log (1000000 / 1568037) := by
    rw [show ((1568037 / 1000000) : ℝ) = ((1000000 / 1568037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
