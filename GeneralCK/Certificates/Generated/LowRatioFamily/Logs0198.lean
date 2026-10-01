import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12672_neg : (40267827 / 500000000) ≤ -Real.log (922622007439 / 1000000000000) ∧
    -Real.log (922622007439 / 1000000000000) ≤ (16107131 / 200000000) := by
  have h := checkLog_sound (w := (77377992561 / 1922622007439)) (n := 12)
    (lo := (40267827 / 500000000)) (hi := (16107131 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 922622007439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 922622007439) = 1/(922622007439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12672 : Bounds (-16107131 / 200000000) (-40267827 / 500000000) (Real.log (922622007439 / 1000000000000)) := by
  have h := reflection_log_12672_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12673_neg : (79181727 / 1000000000) ≤ -Real.log (923872016431 / 1000000000000) ∧
    -Real.log (923872016431 / 1000000000000) ≤ (2474429 / 31250000) := by
  have h := checkLog_sound (w := (76127983569 / 1923872016431)) (n := 12)
    (lo := (79181727 / 1000000000)) (hi := (2474429 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 923872016431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 923872016431) = 1/(923872016431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12673 : Bounds (-2474429 / 31250000) (-79181727 / 1000000000) (Real.log (923872016431 / 1000000000000)) := by
  have h := reflection_log_12673_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12674_neg : (2212913 / 3906250) ≤ -Real.log (31250000000 / 55065594673) ∧
    -Real.log (31250000000 / 55065594673) ≤ (566505729 / 1000000000) := by
  have h := checkLog_sound (w := (23815594673 / 86315594673)) (n := 12)
    (lo := (2212913 / 3906250)) (hi := (566505729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55065594673 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55065594673 / 31250000000) = 1/(31250000000 / 55065594673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12674 : Bounds (2212913 / 3906250) (566505729 / 1000000000) (Real.log (55065594673 / 31250000000)) := by
  have h := reflection_log_12674_neg
  have he : Real.log (55065594673 / 31250000000) = -Real.log (31250000000 / 55065594673) := by
    rw [show ((55065594673 / 31250000000) : ℝ) = ((31250000000 / 55065594673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12675_neg : (71424103 / 125000000) ≤ -Real.log (125000000000 / 221341456657) ∧
    -Real.log (125000000000 / 221341456657) ≤ (22855713 / 40000000) := by
  have h := checkLog_sound (w := (96341456657 / 346341456657)) (n := 12)
    (lo := (71424103 / 125000000)) (hi := (22855713 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((221341456657 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(221341456657 / 125000000000) = 1/(125000000000 / 221341456657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12675 : Bounds (71424103 / 125000000) (22855713 / 40000000) (Real.log (221341456657 / 125000000000)) := by
  have h := reflection_log_12675_neg
  have he : Real.log (221341456657 / 125000000000) = -Real.log (125000000000 / 221341456657) := by
    rw [show ((221341456657 / 125000000000) : ℝ) = ((125000000000 / 221341456657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12676_neg : (1163675881 / 1000000000) ≤ -Real.log (250000000000 / 800420168067) ∧
    -Real.log (250000000000 / 800420168067) ≤ (1163675883 / 1000000000) := by
  have h := checkLog_sound (w := (300420168067 / 1300420168067)) (n := 12)
    (lo := (470528701 / 1000000000)) (hi := (235264351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800420168067 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800420168067 / 500000000000) = 1/(250000000000 / 800420168067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12676 : Bounds (1163675881 / 1000000000) (1163675883 / 1000000000) (Real.log (800420168067 / 250000000000)) := by
  have h := reflection_log_12676_neg
  have he : Real.log (800420168067 / 250000000000) = -Real.log (250000000000 / 800420168067) := by
    rw [show ((800420168067 / 250000000000) : ℝ) = ((250000000000 / 800420168067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12677_neg : (292991229 / 250000000) ≤ -Real.log (500000000000 / 1614164904863) ∧
    -Real.log (500000000000 / 1614164904863) ≤ (585982459 / 500000000) := by
  have h := checkLog_sound (w := (614164904863 / 2614164904863)) (n := 12)
    (lo := (59852217 / 125000000)) (hi := (478817737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1614164904863 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1614164904863 / 1000000000000) = 1/(500000000000 / 1614164904863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12677 : Bounds (292991229 / 250000000) (585982459 / 500000000) (Real.log (1614164904863 / 500000000000)) := by
  have h := reflection_log_12677_neg
  have he : Real.log (1614164904863 / 500000000000) = -Real.log (500000000000 / 1614164904863) := by
    rw [show ((1614164904863 / 500000000000) : ℝ) = ((500000000000 / 1614164904863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12678_neg : (85053547 / 200000000) ≤ -Real.log (100 / 153) ∧
    -Real.log (100 / 153) ≤ (53158467 / 125000000) := by
  have h := checkLog_sound (w := (53 / 253)) (n := 12)
    (lo := (85053547 / 200000000)) (hi := (53158467 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153 / 100) = 1/(100 / 153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12678 : Bounds (85053547 / 200000000) (53158467 / 125000000) (Real.log (153 / 100)) := by
  have h := reflection_log_12678_neg
  have he : Real.log (153 / 100) = -Real.log (100 / 153) := by
    rw [show ((153 / 100) : ℝ) = ((100 / 153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12679_neg : (755022583 / 1000000000) ≤ -Real.log (47 / 100) ∧
    -Real.log (47 / 100) ≤ (151004517 / 200000000) := by
  have h := checkLog_sound (w := (3 / 97)) (n := 12)
    (lo := (61875403 / 1000000000)) (hi := (15468851 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 47) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50 / 47) = 1/(47 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12679 : Bounds (-151004517 / 200000000) (-755022583 / 1000000000) (Real.log (47 / 100)) := by
  have h := reflection_log_12679_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12680_neg : (529859 / 1000000000) ≤ -Real.log (100000 / 100053) ∧
    -Real.log (100000 / 100053) ≤ (26493 / 50000000) := by
  have h := checkLog_sound (w := (53 / 200053)) (n := 12)
    (lo := (529859 / 1000000000)) (hi := (26493 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100053 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100053 / 100000) = 1/(100000 / 100053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12680 : Bounds (529859 / 1000000000) (26493 / 50000000) (Real.log (100053 / 100000)) := by
  have h := reflection_log_12680_neg
  have he : Real.log (100053 / 100000) = -Real.log (100000 / 100053) := by
    rw [show ((100053 / 100000) : ℝ) = ((100000 / 100053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12681_neg : (26507 / 50000000) ≤ -Real.log (99947 / 100000) ∧
    -Real.log (99947 / 100000) ≤ (530141 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 199947)) (n := 12)
    (lo := (26507 / 50000000)) (hi := (530141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99947) = 1/(99947 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12681 : Bounds (-530141 / 1000000000) (-26507 / 50000000) (Real.log (99947 / 100000)) := by
  have h := reflection_log_12681_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12682_neg : (245039671 / 1000000000) ≤ -Real.log (125000 / 159709) ∧
    -Real.log (125000 / 159709) ≤ (30629959 / 125000000) := by
  have h := checkLog_sound (w := (34709 / 284709)) (n := 12)
    (lo := (245039671 / 1000000000)) (hi := (30629959 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159709 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159709 / 125000) = 1/(125000 / 159709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12682 : Bounds (245039671 / 1000000000) (30629959 / 125000000) (Real.log (159709 / 125000)) := by
  have h := reflection_log_12682_neg
  have he : Real.log (159709 / 125000) = -Real.log (125000 / 159709) := by
    rw [show ((159709 / 125000) : ℝ) = ((125000 / 159709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12683_neg : (325275949 / 1000000000) ≤ -Real.log (90291 / 125000) ∧
    -Real.log (90291 / 125000) ≤ (6505519 / 20000000) := by
  have h := checkLog_sound (w := (34709 / 215291)) (n := 12)
    (lo := (325275949 / 1000000000)) (hi := (6505519 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 90291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 90291) = 1/(90291 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12683 : Bounds (-6505519 / 20000000) (-325275949 / 1000000000) (Real.log (90291 / 125000)) := by
  have h := reflection_log_12683_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12684_neg : (123404257 / 500000000) ≤ -Real.log (500000 / 639967) ∧
    -Real.log (500000 / 639967) ≤ (49361703 / 200000000) := by
  have h := checkLog_sound (w := (139967 / 1139967)) (n := 12)
    (lo := (123404257 / 500000000)) (hi := (49361703 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((639967 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(639967 / 500000) = 1/(500000 / 639967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12684 : Bounds (123404257 / 500000000) (49361703 / 200000000) (Real.log (639967 / 500000)) := by
  have h := reflection_log_12684_neg
  have he : Real.log (639967 / 500000) = -Real.log (500000 / 639967) := by
    rw [show ((639967 / 500000) : ℝ) = ((500000 / 639967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12685_neg : (82103101 / 250000000) ≤ -Real.log (360033 / 500000) ∧
    -Real.log (360033 / 500000) ≤ (65682481 / 200000000) := by
  have h := checkLog_sound (w := (139967 / 860033)) (n := 12)
    (lo := (82103101 / 250000000)) (hi := (65682481 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 360033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 360033) = 1/(360033 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12685 : Bounds (-65682481 / 200000000) (-82103101 / 250000000) (Real.log (360033 / 500000)) := by
  have h := reflection_log_12685_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12686_neg : (8160389 / 100000000) ≤ -Real.log (230409238911 / 250000000000) ∧
    -Real.log (230409238911 / 250000000000) ≤ (81603891 / 1000000000) := by
  have h := checkLog_sound (w := (19590761089 / 480409238911)) (n := 12)
    (lo := (8160389 / 100000000)) (hi := (81603891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 230409238911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 230409238911) = 1/(230409238911 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12686 : Bounds (-81603891 / 1000000000) (-8160389 / 100000000) (Real.log (230409238911 / 250000000000)) := by
  have h := reflection_log_12686_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12687_neg : (80236277 / 1000000000) ≤ -Real.log (14420285319 / 15625000000) ∧
    -Real.log (14420285319 / 15625000000) ≤ (40118139 / 500000000) := by
  have h := checkLog_sound (w := (1204714681 / 30045285319)) (n := 12)
    (lo := (80236277 / 1000000000)) (hi := (40118139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 14420285319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 14420285319) = 1/(14420285319 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12687 : Bounds (-40118139 / 500000000) (-80236277 / 1000000000) (Real.log (14420285319 / 15625000000)) := by
  have h := reflection_log_12687_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12688_neg : (570315621 / 1000000000) ≤ -Real.log (125000000000 / 221103155353) ∧
    -Real.log (125000000000 / 221103155353) ≤ (285157811 / 500000000) := by
  have h := checkLog_sound (w := (96103155353 / 346103155353)) (n := 12)
    (lo := (570315621 / 1000000000)) (hi := (285157811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((221103155353 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(221103155353 / 125000000000) = 1/(125000000000 / 221103155353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12688 : Bounds (570315621 / 1000000000) (285157811 / 500000000) (Real.log (221103155353 / 125000000000)) := by
  have h := reflection_log_12688_neg
  have he : Real.log (221103155353 / 125000000000) = -Real.log (125000000000 / 221103155353) := by
    rw [show ((221103155353 / 125000000000) : ℝ) = ((125000000000 / 221103155353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12689_neg : (287610459 / 500000000) ≤ -Real.log (31250000000 / 55547599109) ∧
    -Real.log (31250000000 / 55547599109) ≤ (575220919 / 1000000000) := by
  have h := checkLog_sound (w := (24297599109 / 86797599109)) (n := 12)
    (lo := (287610459 / 500000000)) (hi := (575220919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55547599109 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55547599109 / 31250000000) = 1/(31250000000 / 55547599109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12689 : Bounds (287610459 / 500000000) (575220919 / 1000000000) (Real.log (55547599109 / 31250000000)) := by
  have h := reflection_log_12689_neg
  have he : Real.log (55547599109 / 31250000000) = -Real.log (31250000000 / 55547599109) := by
    rw [show ((55547599109 / 31250000000) : ℝ) = ((31250000000 / 55547599109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12690_neg : (292991229 / 250000000) ≤ -Real.log (250000000000 / 807082452431) ∧
    -Real.log (250000000000 / 807082452431) ≤ (585982459 / 500000000) := by
  have h := checkLog_sound (w := (307082452431 / 1307082452431)) (n := 12)
    (lo := (59852217 / 125000000)) (hi := (478817737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((807082452431 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(807082452431 / 500000000000) = 1/(250000000000 / 807082452431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12690 : Bounds (292991229 / 250000000) (585982459 / 500000000) (Real.log (807082452431 / 250000000000)) := by
  have h := reflection_log_12690_neg
  have he : Real.log (807082452431 / 250000000000) = -Real.log (250000000000 / 807082452431) := by
    rw [show ((807082452431 / 250000000000) : ℝ) = ((250000000000 / 807082452431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12691_neg : (1180290319 / 1000000000) ≤ -Real.log (500000000000 / 1627659574469) ∧
    -Real.log (500000000000 / 1627659574469) ≤ (1180290321 / 1000000000) := by
  have h := checkLog_sound (w := (627659574469 / 2627659574469)) (n := 12)
    (lo := (487143139 / 1000000000)) (hi := (24357157 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1627659574469 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1627659574469 / 1000000000000) = 1/(500000000000 / 1627659574469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12691 : Bounds (1180290319 / 1000000000) (1180290321 / 1000000000) (Real.log (1627659574469 / 500000000000)) := by
  have h := reflection_log_12691_neg
  have he : Real.log (1627659574469 / 500000000000) = -Real.log (500000000000 / 1627659574469) := by
    rw [show ((1627659574469 / 500000000000) : ℝ) = ((500000000000 / 1627659574469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12692_neg : (427226599 / 1000000000) ≤ -Real.log (1000 / 1533) ∧
    -Real.log (1000 / 1533) ≤ (2136133 / 5000000) := by
  have h := checkLog_sound (w := (533 / 2533)) (n := 12)
    (lo := (427226599 / 1000000000)) (hi := (2136133 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1533 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1533 / 1000) = 1/(1000 / 1533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12692 : Bounds (427226599 / 1000000000) (2136133 / 5000000) (Real.log (1533 / 1000)) := by
  have h := reflection_log_12692_neg
  have he : Real.log (1533 / 1000) = -Real.log (1000 / 1533) := by
    rw [show ((1533 / 1000) : ℝ) = ((1000 / 1533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12693_neg : (38071301 / 50000000) ≤ -Real.log (467 / 1000) ∧
    -Real.log (467 / 1000) ≤ (380713011 / 500000000) := by
  have h := checkLog_sound (w := (33 / 967)) (n := 12)
    (lo := (1706971 / 25000000)) (hi := (68278841 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 467) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 467) = 1/(467 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12693 : Bounds (-380713011 / 500000000) (-38071301 / 50000000) (Real.log (467 / 1000)) := by
  have h := reflection_log_12693_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12694_neg : (266429 / 500000000) ≤ -Real.log (1000000 / 1000533) ∧
    -Real.log (1000000 / 1000533) ≤ (532859 / 1000000000) := by
  have h := checkLog_sound (w := (533 / 2000533)) (n := 12)
    (lo := (266429 / 500000000)) (hi := (532859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000533 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000533 / 1000000) = 1/(1000000 / 1000533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12694 : Bounds (266429 / 500000000) (532859 / 1000000000) (Real.log (1000533 / 1000000)) := by
  have h := reflection_log_12694_neg
  have he : Real.log (1000533 / 1000000) = -Real.log (1000000 / 1000533) := by
    rw [show ((1000533 / 1000000) : ℝ) = ((1000000 / 1000533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12695_neg : (266571 / 500000000) ≤ -Real.log (999467 / 1000000) ∧
    -Real.log (999467 / 1000000) ≤ (533143 / 1000000000) := by
  have h := checkLog_sound (w := (533 / 1999467)) (n := 12)
    (lo := (266571 / 500000000)) (hi := (533143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999467) = 1/(999467 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12695 : Bounds (-533143 / 1000000000) (-266571 / 500000000) (Real.log (999467 / 1000000)) := by
  have h := reflection_log_12695_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12696_neg : (123209287 / 500000000) ≤ -Real.log (200000 / 255887) ∧
    -Real.log (200000 / 255887) ≤ (9856743 / 40000000) := by
  have h := checkLog_sound (w := (55887 / 455887)) (n := 12)
    (lo := (123209287 / 500000000)) (hi := (9856743 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((255887 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(255887 / 200000) = 1/(200000 / 255887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12696 : Bounds (123209287 / 500000000) (9856743 / 40000000) (Real.log (255887 / 200000)) := by
  have h := reflection_log_12696_neg
  have he : Real.log (255887 / 200000) = -Real.log (200000 / 255887) := by
    rw [show ((255887 / 200000) : ℝ) = ((200000 / 255887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12697_neg : (81929913 / 250000000) ≤ -Real.log (144113 / 200000) ∧
    -Real.log (144113 / 200000) ≤ (327719653 / 1000000000) := by
  have h := checkLog_sound (w := (55887 / 344113)) (n := 12)
    (lo := (81929913 / 250000000)) (hi := (327719653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 144113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 144113) = 1/(144113 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12697 : Bounds (-327719653 / 1000000000) (-81929913 / 250000000) (Real.log (144113 / 200000)) := by
  have h := reflection_log_12697_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12698_neg : (124094831 / 500000000) ≤ -Real.log (1000000 / 1281703) ∧
    -Real.log (1000000 / 1281703) ≤ (248189663 / 1000000000) := by
  have h := checkLog_sound (w := (281703 / 2281703)) (n := 12)
    (lo := (124094831 / 500000000)) (hi := (248189663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1281703 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1281703 / 1000000) = 1/(1000000 / 1281703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12698 : Bounds (124094831 / 500000000) (248189663 / 1000000000) (Real.log (1281703 / 1000000)) := by
  have h := reflection_log_12698_neg
  have he : Real.log (1281703 / 1000000) = -Real.log (1000000 / 1281703) := by
    rw [show ((1281703 / 1000000) : ℝ) = ((1000000 / 1281703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12699_neg : (165436073 / 500000000) ≤ -Real.log (718297 / 1000000) ∧
    -Real.log (718297 / 1000000) ≤ (330872147 / 1000000000) := by
  have h := checkLog_sound (w := (281703 / 1718297)) (n := 12)
    (lo := (165436073 / 500000000)) (hi := (330872147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 718297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 718297) = 1/(718297 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12699 : Bounds (-330872147 / 1000000000) (-165436073 / 500000000) (Real.log (718297 / 1000000)) := by
  have h := reflection_log_12699_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12700_neg : (20670621 / 250000000) ≤ -Real.log (920643419791 / 1000000000000) ∧
    -Real.log (920643419791 / 1000000000000) ≤ (16536497 / 200000000) := by
  have h := checkLog_sound (w := (79356580209 / 1920643419791)) (n := 12)
    (lo := (20670621 / 250000000)) (hi := (16536497 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 920643419791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 920643419791) = 1/(920643419791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12700 : Bounds (-16536497 / 200000000) (-20670621 / 250000000) (Real.log (920643419791 / 1000000000000)) := by
  have h := reflection_log_12700_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12701_neg : (40650539 / 500000000) ≤ -Real.log (36876643231 / 40000000000) ∧
    -Real.log (36876643231 / 40000000000) ≤ (81301079 / 1000000000) := by
  have h := checkLog_sound (w := (3123356769 / 76876643231)) (n := 12)
    (lo := (40650539 / 500000000)) (hi := (81301079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 36876643231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 36876643231) = 1/(36876643231 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12701 : Bounds (-81301079 / 1000000000) (-40650539 / 500000000) (Real.log (36876643231 / 40000000000)) := by
  have h := reflection_log_12701_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12702_neg : (287069113 / 500000000) ≤ -Real.log (100000000000 / 177559970301) ∧
    -Real.log (100000000000 / 177559970301) ≤ (574138227 / 1000000000) := by
  have h := checkLog_sound (w := (77559970301 / 277559970301)) (n := 12)
    (lo := (287069113 / 500000000)) (hi := (574138227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((177559970301 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(177559970301 / 100000000000) = 1/(100000000000 / 177559970301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12702 : Bounds (287069113 / 500000000) (574138227 / 1000000000) (Real.log (177559970301 / 100000000000)) := by
  have h := reflection_log_12702_neg
  have he : Real.log (177559970301 / 100000000000) = -Real.log (100000000000 / 177559970301) := by
    rw [show ((177559970301 / 100000000000) : ℝ) = ((100000000000 / 177559970301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12703_neg : (36191363 / 62500000) ≤ -Real.log (500000000000 / 892181785529) ∧
    -Real.log (500000000000 / 892181785529) ≤ (579061809 / 1000000000) := by
  have h := checkLog_sound (w := (392181785529 / 1392181785529)) (n := 12)
    (lo := (36191363 / 62500000)) (hi := (579061809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((892181785529 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(892181785529 / 500000000000) = 1/(500000000000 / 892181785529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12703 : Bounds (36191363 / 62500000) (579061809 / 1000000000) (Real.log (892181785529 / 500000000000)) := by
  have h := reflection_log_12703_neg
  have he : Real.log (892181785529 / 500000000000) = -Real.log (500000000000 / 892181785529) := by
    rw [show ((892181785529 / 500000000000) : ℝ) = ((500000000000 / 892181785529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12704_neg : (1180290319 / 1000000000) ≤ -Real.log (125000000000 / 406914893617) ∧
    -Real.log (125000000000 / 406914893617) ≤ (1180290321 / 1000000000) := by
  have h := checkLog_sound (w := (156914893617 / 656914893617)) (n := 12)
    (lo := (487143139 / 1000000000)) (hi := (24357157 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((406914893617 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(406914893617 / 250000000000) = 1/(125000000000 / 406914893617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12704 : Bounds (1180290319 / 1000000000) (1180290321 / 1000000000) (Real.log (406914893617 / 125000000000)) := by
  have h := reflection_log_12704_neg
  have he : Real.log (406914893617 / 125000000000) = -Real.log (125000000000 / 406914893617) := by
    rw [show ((406914893617 / 125000000000) : ℝ) = ((125000000000 / 406914893617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12705_neg : (59432631 / 50000000) ≤ -Real.log (500000000000 / 1641327623127) ∧
    -Real.log (500000000000 / 1641327623127) ≤ (594326311 / 500000000) := by
  have h := checkLog_sound (w := (641327623127 / 2641327623127)) (n := 12)
    (lo := (3096909 / 6250000)) (hi := (495505441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1641327623127 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1641327623127 / 1000000000000) = 1/(500000000000 / 1641327623127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12705 : Bounds (59432631 / 50000000) (594326311 / 500000000) (Real.log (1641327623127 / 500000000000)) := by
  have h := reflection_log_12705_neg
  have he : Real.log (1641327623127 / 500000000000) = -Real.log (500000000000 / 1641327623127) := by
    rw [show ((1641327623127 / 500000000000) : ℝ) = ((500000000000 / 1641327623127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12706_neg : (214590817 / 500000000) ≤ -Real.log (125 / 192) ∧
    -Real.log (125 / 192) ≤ (85836327 / 200000000) := by
  have h := checkLog_sound (w := (67 / 317)) (n := 12)
    (lo := (214590817 / 500000000)) (hi := (85836327 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((192 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(192 / 125) = 1/(125 / 192) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12706 : Bounds (214590817 / 500000000) (85836327 / 200000000) (Real.log (192 / 125)) := by
  have h := reflection_log_12706_neg
  have he : Real.log (192 / 125) = -Real.log (125 / 192) := by
    rw [show ((192 / 125) : ℝ) = ((125 / 192) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12707_neg : (383935363 / 500000000) ≤ -Real.log (58 / 125) ∧
    -Real.log (58 / 125) ≤ (95983841 / 125000000) := by
  have h := checkLog_sound (w := (9 / 241)) (n := 12)
    (lo := (37361773 / 500000000)) (hi := (74723547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 116) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 116) = 1/(58 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12707 : Bounds (-95983841 / 125000000) (-383935363 / 500000000) (Real.log (58 / 125)) := by
  have h := reflection_log_12707_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12708_neg : (33491 / 62500000) ≤ -Real.log (125000 / 125067) ∧
    -Real.log (125000 / 125067) ≤ (535857 / 1000000000) := by
  have h := checkLog_sound (w := (67 / 250067)) (n := 12)
    (lo := (33491 / 62500000)) (hi := (535857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125067 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125067 / 125000) = 1/(125000 / 125067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12708 : Bounds (33491 / 62500000) (535857 / 1000000000) (Real.log (125067 / 125000)) := by
  have h := reflection_log_12708_neg
  have he : Real.log (125067 / 125000) = -Real.log (125000 / 125067) := by
    rw [show ((125067 / 125000) : ℝ) = ((125000 / 125067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12709_neg : (536143 / 1000000000) ≤ -Real.log (124933 / 125000) ∧
    -Real.log (124933 / 125000) ≤ (33509 / 62500000) := by
  have h := checkLog_sound (w := (67 / 249933)) (n := 12)
    (lo := (536143 / 1000000000)) (hi := (33509 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124933) = 1/(124933 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12709 : Bounds (-33509 / 62500000) (-536143 / 1000000000) (Real.log (124933 / 125000)) := by
  have h := reflection_log_12709_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12710_neg : (247797919 / 1000000000) ≤ -Real.log (1000000 / 1281201) ∧
    -Real.log (1000000 / 1281201) ≤ (1548737 / 6250000) := by
  have h := checkLog_sound (w := (281201 / 2281201)) (n := 12)
    (lo := (247797919 / 1000000000)) (hi := (1548737 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1281201 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1281201 / 1000000) = 1/(1000000 / 1281201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12710 : Bounds (247797919 / 1000000000) (1548737 / 6250000) (Real.log (1281201 / 1000000)) := by
  have h := reflection_log_12710_neg
  have he : Real.log (1281201 / 1000000) = -Real.log (1000000 / 1281201) := by
    rw [show ((1281201 / 1000000) : ℝ) = ((1000000 / 1281201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12711_neg : (66034703 / 200000000) ≤ -Real.log (718799 / 1000000) ∧
    -Real.log (718799 / 1000000) ≤ (82543379 / 250000000) := by
  have h := checkLog_sound (w := (281201 / 1718799)) (n := 12)
    (lo := (66034703 / 200000000)) (hi := (82543379 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 718799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 718799) = 1/(718799 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12711 : Bounds (-82543379 / 250000000) (-66034703 / 200000000) (Real.log (718799 / 1000000)) := by
  have h := reflection_log_12711_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12712_neg : (249571243 / 1000000000) ≤ -Real.log (40000 / 51339) ∧
    -Real.log (40000 / 51339) ≤ (62392811 / 250000000) := by
  have h := checkLog_sound (w := (11339 / 91339)) (n := 12)
    (lo := (249571243 / 1000000000)) (hi := (62392811 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51339 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51339 / 40000) = 1/(40000 / 51339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12712 : Bounds (249571243 / 1000000000) (62392811 / 250000000) (Real.log (51339 / 40000)) := by
  have h := reflection_log_12712_neg
  have he : Real.log (51339 / 40000) = -Real.log (40000 / 51339) := by
    rw [show ((51339 / 40000) : ℝ) = ((40000 / 51339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12713_neg : (16667107 / 50000000) ≤ -Real.log (28661 / 40000) ∧
    -Real.log (28661 / 40000) ≤ (333342141 / 1000000000) := by
  have h := checkLog_sound (w := (11339 / 68661)) (n := 12)
    (lo := (16667107 / 50000000)) (hi := (333342141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 28661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 28661) = 1/(28661 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12713 : Bounds (-333342141 / 1000000000) (-16667107 / 50000000) (Real.log (28661 / 40000)) := by
  have h := reflection_log_12713_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12714_neg : (83770897 / 1000000000) ≤ -Real.log (1471427079 / 1600000000) ∧
    -Real.log (1471427079 / 1600000000) ≤ (41885449 / 500000000) := by
  have h := checkLog_sound (w := (128572921 / 3071427079)) (n := 12)
    (lo := (83770897 / 1000000000)) (hi := (41885449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1471427079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1471427079) = 1/(1471427079 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12714 : Bounds (-41885449 / 500000000) (-83770897 / 1000000000) (Real.log (1471427079 / 1600000000)) := by
  have h := reflection_log_12714_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12715_neg : (20593899 / 250000000) ≤ -Real.log (920925997599 / 1000000000000) ∧
    -Real.log (920925997599 / 1000000000000) ≤ (82375597 / 1000000000) := by
  have h := checkLog_sound (w := (79074002401 / 1920925997599)) (n := 12)
    (lo := (20593899 / 250000000)) (hi := (82375597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 920925997599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 920925997599) = 1/(920925997599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12715 : Bounds (-82375597 / 1000000000) (-20593899 / 250000000) (Real.log (920925997599 / 1000000000000)) := by
  have h := reflection_log_12715_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12716_neg : (288985717 / 500000000) ≤ -Real.log (50000000000 / 89120950363) ∧
    -Real.log (50000000000 / 89120950363) ≤ (115594287 / 200000000) := by
  have h := checkLog_sound (w := (39120950363 / 139120950363)) (n := 12)
    (lo := (288985717 / 500000000)) (hi := (115594287 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89120950363 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89120950363 / 50000000000) = 1/(50000000000 / 89120950363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12716 : Bounds (288985717 / 500000000) (115594287 / 200000000) (Real.log (89120950363 / 50000000000)) := by
  have h := reflection_log_12716_neg
  have he : Real.log (89120950363 / 50000000000) = -Real.log (50000000000 / 89120950363) := by
    rw [show ((89120950363 / 50000000000) : ℝ) = ((50000000000 / 89120950363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12717_neg : (582913383 / 1000000000) ≤ -Real.log (250000000000 / 447812358257) ∧
    -Real.log (250000000000 / 447812358257) ≤ (72864173 / 125000000) := by
  have h := checkLog_sound (w := (197812358257 / 697812358257)) (n := 12)
    (lo := (582913383 / 1000000000)) (hi := (72864173 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((447812358257 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(447812358257 / 250000000000) = 1/(250000000000 / 447812358257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12717 : Bounds (582913383 / 1000000000) (72864173 / 125000000) (Real.log (447812358257 / 250000000000)) := by
  have h := reflection_log_12717_neg
  have he : Real.log (447812358257 / 250000000000) = -Real.log (250000000000 / 447812358257) := by
    rw [show ((447812358257 / 250000000000) : ℝ) = ((250000000000 / 447812358257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12718_neg : (59432631 / 50000000) ≤ -Real.log (250000000000 / 820663811563) ∧
    -Real.log (250000000000 / 820663811563) ≤ (594326311 / 500000000) := by
  have h := checkLog_sound (w := (320663811563 / 1320663811563)) (n := 12)
    (lo := (3096909 / 6250000)) (hi := (495505441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((820663811563 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(820663811563 / 500000000000) = 1/(250000000000 / 820663811563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12718 : Bounds (59432631 / 50000000) (594326311 / 500000000) (Real.log (820663811563 / 250000000000)) := by
  have h := reflection_log_12718_neg
  have he : Real.log (820663811563 / 250000000000) = -Real.log (250000000000 / 820663811563) := by
    rw [show ((820663811563 / 250000000000) : ℝ) = ((250000000000 / 820663811563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12719_neg : (29926309 / 25000000) ≤ -Real.log (250000000000 / 827586206897) ∧
    -Real.log (250000000000 / 827586206897) ≤ (598526181 / 500000000) := by
  have h := checkLog_sound (w := (327586206897 / 1327586206897)) (n := 12)
    (lo := (25195259 / 50000000)) (hi := (503905181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((827586206897 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(827586206897 / 500000000000) = 1/(250000000000 / 827586206897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12719 : Bounds (29926309 / 25000000) (598526181 / 500000000) (Real.log (827586206897 / 250000000000)) := by
  have h := reflection_log_12719_neg
  have he : Real.log (827586206897 / 250000000000) = -Real.log (250000000000 / 827586206897) := by
    rw [show ((827586206897 / 250000000000) : ℝ) = ((250000000000 / 827586206897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12720_neg : (215566427 / 500000000) ≤ -Real.log (1000 / 1539) ∧
    -Real.log (1000 / 1539) ≤ (86226571 / 200000000) := by
  have h := checkLog_sound (w := (539 / 2539)) (n := 12)
    (lo := (215566427 / 500000000)) (hi := (86226571 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1539 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1539 / 1000) = 1/(1000 / 1539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12720 : Bounds (215566427 / 500000000) (86226571 / 200000000) (Real.log (1539 / 1000)) := by
  have h := reflection_log_12720_neg
  have he : Real.log (1539 / 1000) = -Real.log (1000 / 1539) := by
    rw [show ((1539 / 1000) : ℝ) = ((1000 / 1539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12721_neg : (154871447 / 200000000) ≤ -Real.log (461 / 1000) ∧
    -Real.log (461 / 1000) ≤ (774357237 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 961)) (n := 12)
    (lo := (16242011 / 200000000)) (hi := (10151257 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 461) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 461) = 1/(461 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12721 : Bounds (-774357237 / 1000000000) (-154871447 / 200000000) (Real.log (461 / 1000)) := by
  have h := reflection_log_12721_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12722_neg : (269427 / 500000000) ≤ -Real.log (1000000 / 1000539) ∧
    -Real.log (1000000 / 1000539) ≤ (107771 / 200000000) := by
  have h := checkLog_sound (w := (539 / 2000539)) (n := 12)
    (lo := (269427 / 500000000)) (hi := (107771 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000539 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000539 / 1000000) = 1/(1000000 / 1000539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12722 : Bounds (269427 / 500000000) (107771 / 200000000) (Real.log (1000539 / 1000000)) := by
  have h := reflection_log_12722_neg
  have he : Real.log (1000539 / 1000000) = -Real.log (1000000 / 1000539) := by
    rw [show ((1000539 / 1000000) : ℝ) = ((1000000 / 1000539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12723_neg : (107829 / 200000000) ≤ -Real.log (999461 / 1000000) ∧
    -Real.log (999461 / 1000000) ≤ (269573 / 500000000) := by
  have h := checkLog_sound (w := (539 / 1999461)) (n := 12)
    (lo := (107829 / 200000000)) (hi := (269573 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999461) = 1/(999461 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12723 : Bounds (-269573 / 500000000) (-107829 / 200000000) (Real.log (999461 / 1000000)) := by
  have h := reflection_log_12723_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12724_neg : (124589241 / 500000000) ≤ -Real.log (1000000 / 1282971) ∧
    -Real.log (1000000 / 1282971) ≤ (249178483 / 1000000000) := by
  have h := checkLog_sound (w := (282971 / 2282971)) (n := 12)
    (lo := (124589241 / 500000000)) (hi := (249178483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1282971 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1282971 / 1000000) = 1/(1000000 / 1282971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12724 : Bounds (124589241 / 500000000) (249178483 / 1000000000) (Real.log (1282971 / 1000000)) := by
  have h := reflection_log_12724_neg
  have he : Real.log (1282971 / 1000000) = -Real.log (1000000 / 1282971) := by
    rw [show ((1282971 / 1000000) : ℝ) = ((1000000 / 1282971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12725_neg : (20789937 / 62500000) ≤ -Real.log (717029 / 1000000) ∧
    -Real.log (717029 / 1000000) ≤ (332638993 / 1000000000) := by
  have h := checkLog_sound (w := (282971 / 1717029)) (n := 12)
    (lo := (20789937 / 62500000)) (hi := (332638993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 717029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 717029) = 1/(717029 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12725 : Bounds (-332638993 / 1000000000) (-20789937 / 62500000) (Real.log (717029 / 1000000)) := by
  have h := reflection_log_12725_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12726_neg : (25095403 / 100000000) ≤ -Real.log (1000000 / 1285251) ∧
    -Real.log (1000000 / 1285251) ≤ (250954031 / 1000000000) := by
  have h := checkLog_sound (w := (285251 / 2285251)) (n := 12)
    (lo := (25095403 / 100000000)) (hi := (250954031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1285251 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1285251 / 1000000) = 1/(1000000 / 1285251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12726 : Bounds (25095403 / 100000000) (250954031 / 1000000000) (Real.log (1285251 / 1000000)) := by
  have h := reflection_log_12726_neg
  have he : Real.log (1285251 / 1000000) = -Real.log (1000000 / 1285251) := by
    rw [show ((1285251 / 1000000) : ℝ) = ((1000000 / 1285251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12727_neg : (167911923 / 500000000) ≤ -Real.log (714749 / 1000000) ∧
    -Real.log (714749 / 1000000) ≤ (335823847 / 1000000000) := by
  have h := checkLog_sound (w := (285251 / 1714749)) (n := 12)
    (lo := (167911923 / 500000000)) (hi := (335823847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 714749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 714749) = 1/(714749 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12727 : Bounds (-335823847 / 1000000000) (-167911923 / 500000000) (Real.log (714749 / 1000000)) := by
  have h := reflection_log_12727_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12728_neg : (10608727 / 125000000) ≤ -Real.log (918631866999 / 1000000000000) ∧
    -Real.log (918631866999 / 1000000000000) ≤ (84869817 / 1000000000) := by
  have h := checkLog_sound (w := (81368133001 / 1918631866999)) (n := 12)
    (lo := (10608727 / 125000000)) (hi := (84869817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 918631866999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 918631866999) = 1/(918631866999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12728 : Bounds (-84869817 / 1000000000) (-10608727 / 125000000) (Real.log (918631866999 / 1000000000000)) := by
  have h := reflection_log_12728_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12729_neg : (8346051 / 100000000) ≤ -Real.log (919927413159 / 1000000000000) ∧
    -Real.log (919927413159 / 1000000000000) ≤ (83460511 / 1000000000) := by
  have h := checkLog_sound (w := (80072586841 / 1919927413159)) (n := 12)
    (lo := (8346051 / 100000000)) (hi := (83460511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 919927413159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 919927413159) = 1/(919927413159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12729 : Bounds (-83460511 / 1000000000) (-8346051 / 100000000) (Real.log (919927413159 / 1000000000000)) := by
  have h := reflection_log_12729_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12730_neg : (23272699 / 40000000) ≤ -Real.log (100000000000 / 178928746257) ∧
    -Real.log (100000000000 / 178928746257) ≤ (145454369 / 250000000) := by
  have h := checkLog_sound (w := (78928746257 / 278928746257)) (n := 12)
    (lo := (23272699 / 40000000)) (hi := (145454369 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178928746257 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178928746257 / 100000000000) = 1/(100000000000 / 178928746257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12730 : Bounds (23272699 / 40000000) (145454369 / 250000000) (Real.log (178928746257 / 100000000000)) := by
  have h := reflection_log_12730_neg
  have he : Real.log (178928746257 / 100000000000) = -Real.log (100000000000 / 178928746257) := by
    rw [show ((178928746257 / 100000000000) : ℝ) = ((100000000000 / 178928746257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12731_neg : (146694469 / 250000000) ≤ -Real.log (500000000000 / 899092548573) ∧
    -Real.log (500000000000 / 899092548573) ≤ (586777877 / 1000000000) := by
  have h := checkLog_sound (w := (399092548573 / 1399092548573)) (n := 12)
    (lo := (146694469 / 250000000)) (hi := (586777877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((899092548573 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(899092548573 / 500000000000) = 1/(500000000000 / 899092548573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12731 : Bounds (146694469 / 250000000) (586777877 / 1000000000) (Real.log (899092548573 / 500000000000)) := by
  have h := reflection_log_12731_neg
  have he : Real.log (899092548573 / 500000000000) = -Real.log (500000000000 / 899092548573) := by
    rw [show ((899092548573 / 500000000000) : ℝ) = ((500000000000 / 899092548573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12732_neg : (29926309 / 25000000) ≤ -Real.log (500000000000 / 1655172413793) ∧
    -Real.log (500000000000 / 1655172413793) ≤ (598526181 / 500000000) := by
  have h := checkLog_sound (w := (655172413793 / 2655172413793)) (n := 12)
    (lo := (25195259 / 50000000)) (hi := (503905181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1655172413793 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1655172413793 / 1000000000000) = 1/(500000000000 / 1655172413793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12732 : Bounds (29926309 / 25000000) (598526181 / 500000000) (Real.log (1655172413793 / 500000000000)) := by
  have h := reflection_log_12732_neg
  have he : Real.log (1655172413793 / 500000000000) = -Real.log (500000000000 / 1655172413793) := by
    rw [show ((1655172413793 / 500000000000) : ℝ) = ((500000000000 / 1655172413793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12733_neg : (120549009 / 100000000) ≤ -Real.log (125000000000 / 417299349241) ∧
    -Real.log (125000000000 / 417299349241) ≤ (301372523 / 250000000) := by
  have h := checkLog_sound (w := (167299349241 / 667299349241)) (n := 12)
    (lo := (51234291 / 100000000)) (hi := (512342911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((417299349241 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(417299349241 / 250000000000) = 1/(125000000000 / 417299349241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12733 : Bounds (120549009 / 100000000) (301372523 / 250000000) (Real.log (417299349241 / 125000000000)) := by
  have h := reflection_log_12733_neg
  have he : Real.log (417299349241 / 125000000000) = -Real.log (125000000000 / 417299349241) := by
    rw [show ((417299349241 / 125000000000) : ℝ) = ((125000000000 / 417299349241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12734_neg : (17323211 / 40000000) ≤ -Real.log (500 / 771) ∧
    -Real.log (500 / 771) ≤ (108270069 / 250000000) := by
  have h := checkLog_sound (w := (271 / 1271)) (n := 12)
    (lo := (17323211 / 40000000)) (hi := (108270069 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((771 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(771 / 500) = 1/(500 / 771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12734 : Bounds (17323211 / 40000000) (108270069 / 250000000) (Real.log (771 / 500)) := by
  have h := reflection_log_12734_neg
  have he : Real.log (771 / 500) = -Real.log (500 / 771) := by
    rw [show ((771 / 500) : ℝ) = ((500 / 771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12735_neg : (390443047 / 500000000) ≤ -Real.log (229 / 500) ∧
    -Real.log (229 / 500) ≤ (48805381 / 62500000) := by
  have h := checkLog_sound (w := (21 / 479)) (n := 12)
    (lo := (43869457 / 500000000)) (hi := (17547783 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 229) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 229) = 1/(229 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12735 : Bounds (-48805381 / 62500000) (-390443047 / 500000000) (Real.log (229 / 500)) := by
  have h := reflection_log_12735_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
