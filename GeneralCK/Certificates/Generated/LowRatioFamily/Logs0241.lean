import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_15424_neg : (2510342813 / 500000000) ≤ -Real.log (33 / 5000) ∧
    -Real.log (33 / 5000) ≤ (2510342817 / 500000000) := by
  have h := checkLog_sound (w := (97 / 1153)) (n := 12)
    (lo := (84327683 / 500000000)) (hi := (168655367 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 528) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 528) = 1/(33 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15424 : Bounds (-2510342817 / 500000000) (-2510342813 / 500000000) (Real.log (33 / 5000)) := by
  have h := reflection_log_15424_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15425_neg : (496453 / 500000000) ≤ -Real.log (5000000 / 5004967) ∧
    -Real.log (5000000 / 5004967) ≤ (992907 / 1000000000) := by
  have h := checkLog_sound (w := (4967 / 10004967)) (n := 12)
    (lo := (496453 / 500000000)) (hi := (992907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004967 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004967 / 5000000) = 1/(5000000 / 5004967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15425 : Bounds (496453 / 500000000) (992907 / 1000000000) (Real.log (5004967 / 5000000)) := by
  have h := reflection_log_15425_neg
  have he : Real.log (5004967 / 5000000) = -Real.log (5000000 / 5004967) := by
    rw [show ((5004967 / 5000000) : ℝ) = ((5000000 / 5004967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15426_neg : (993893 / 1000000000) ≤ -Real.log (4995033 / 5000000) ∧
    -Real.log (4995033 / 5000000) ≤ (496947 / 500000000) := by
  have h := checkLog_sound (w := (4967 / 9995033)) (n := 12)
    (lo := (993893 / 1000000000)) (hi := (496947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995033) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995033) = 1/(4995033 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15426 : Bounds (-496947 / 500000000) (-993893 / 1000000000) (Real.log (4995033 / 5000000)) := by
  have h := reflection_log_15426_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15427_neg : (498645749 / 1000000000) ≤ -Real.log (100000 / 164649) ∧
    -Real.log (100000 / 164649) ≤ (1994583 / 4000000) := by
  have h := checkLog_sound (w := (64649 / 264649)) (n := 12)
    (lo := (498645749 / 1000000000)) (hi := (1994583 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164649 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164649 / 100000) = 1/(100000 / 164649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15427 : Bounds (498645749 / 1000000000) (1994583 / 4000000) (Real.log (164649 / 100000)) := by
  have h := reflection_log_15427_neg
  have he : Real.log (164649 / 100000) = -Real.log (100000 / 164649) := by
    rw [show ((164649 / 100000) : ℝ) = ((100000 / 164649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15428_neg : (64990219 / 62500000) ≤ -Real.log (35351 / 100000) ∧
    -Real.log (35351 / 100000) ≤ (519921753 / 500000000) := by
  have h := checkLog_sound (w := (14649 / 85351)) (n := 12)
    (lo := (86674081 / 250000000)) (hi := (13867853 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35351) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 35351) = 1/(35351 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15428 : Bounds (-519921753 / 500000000) (-64990219 / 62500000) (Real.log (35351 / 100000)) := by
  have h := reflection_log_15428_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15429_neg : (49921589 / 100000000) ≤ -Real.log (1000000 / 1647429) ∧
    -Real.log (1000000 / 1647429) ≤ (499215891 / 1000000000) := by
  have h := checkLog_sound (w := (647429 / 2647429)) (n := 12)
    (lo := (49921589 / 100000000)) (hi := (499215891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1647429 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1647429 / 1000000) = 1/(1000000 / 1647429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15429 : Bounds (49921589 / 100000000) (499215891 / 1000000000) (Real.log (1647429 / 1000000)) := by
  have h := reflection_log_15429_neg
  have he : Real.log (1647429 / 1000000) = -Real.log (1000000 / 1647429) := by
    rw [show ((1647429 / 1000000) : ℝ) = ((1000000 / 1647429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15430_neg : (521251629 / 500000000) ≤ -Real.log (352571 / 1000000) ∧
    -Real.log (352571 / 1000000) ≤ (52125163 / 50000000) := by
  have h := checkLog_sound (w := (147429 / 852571)) (n := 12)
    (lo := (174678039 / 500000000)) (hi := (349356079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 352571) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 352571) = 1/(352571 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15430 : Bounds (-52125163 / 50000000) (-521251629 / 500000000) (Real.log (352571 / 1000000)) := by
  have h := reflection_log_15430_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15431_neg : (543287367 / 1000000000) ≤ -Real.log (580835689959 / 1000000000000) ∧
    -Real.log (580835689959 / 1000000000000) ≤ (67910921 / 125000000) := by
  have h := checkLog_sound (w := (419164310041 / 1580835689959)) (n := 12)
    (lo := (543287367 / 1000000000)) (hi := (67910921 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 580835689959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 580835689959) = 1/(580835689959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15431 : Bounds (-67910921 / 125000000) (-543287367 / 1000000000) (Real.log (580835689959 / 1000000000000)) := by
  have h := reflection_log_15431_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15432_neg : (135299439 / 250000000) ≤ -Real.log (5820506799 / 10000000000) ∧
    -Real.log (5820506799 / 10000000000) ≤ (541197757 / 1000000000) := by
  have h := checkLog_sound (w := (4179493201 / 15820506799)) (n := 12)
    (lo := (135299439 / 250000000)) (hi := (541197757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 5820506799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 5820506799) = 1/(5820506799 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15432 : Bounds (-541197757 / 1000000000) (-135299439 / 250000000) (Real.log (5820506799 / 10000000000)) := by
  have h := reflection_log_15432_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15433_neg : (1538489253 / 1000000000) ≤ -Real.log (500000000000 / 2328774292099) ∧
    -Real.log (500000000000 / 2328774292099) ≤ (192311157 / 125000000) := by
  have h := checkLog_sound (w := (328774292099 / 4328774292099)) (n := 12)
    (lo := (152194893 / 1000000000)) (hi := (76097447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2328774292099 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2328774292099 / 2000000000000) = 1/(500000000000 / 2328774292099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15433 : Bounds (1538489253 / 1000000000) (192311157 / 125000000) (Real.log (2328774292099 / 500000000000)) := by
  have h := reflection_log_15433_neg
  have he : Real.log (2328774292099 / 500000000000) = -Real.log (500000000000 / 2328774292099) := by
    rw [show ((2328774292099 / 500000000000) : ℝ) = ((500000000000 / 2328774292099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15434_neg : (385429787 / 250000000) ≤ -Real.log (500000000000 / 2336308147863) ∧
    -Real.log (500000000000 / 2336308147863) ≤ (1541719151 / 1000000000) := by
  have h := checkLog_sound (w := (336308147863 / 4336308147863)) (n := 12)
    (lo := (38856197 / 250000000)) (hi := (155424789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2336308147863 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2336308147863 / 2000000000000) = 1/(500000000000 / 2336308147863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15434 : Bounds (385429787 / 250000000) (1541719151 / 1000000000) (Real.log (2336308147863 / 500000000000)) := by
  have h := reflection_log_15434_neg
  have he : Real.log (2336308147863 / 500000000000) = -Real.log (500000000000 / 2336308147863) := by
    rw [show ((2336308147863 / 500000000000) : ℝ) = ((500000000000 / 2336308147863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15435_neg : (5680574049 / 1000000000) ≤ -Real.log (500000000000 / 146558823529411) ∧
    -Real.log (500000000000 / 146558823529411) ≤ (2840287029 / 500000000) := by
  have h := checkLog_sound (w := (18558823529411 / 274558823529411)) (n := 12)
    (lo := (135396609 / 1000000000)) (hi := (13539661 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146558823529411 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(146558823529411 / 128000000000000) = 1/(500000000000 / 146558823529411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15435 : Bounds (5680574049 / 1000000000) (2840287029 / 500000000) (Real.log (146558823529411 / 500000000000)) := by
  have h := reflection_log_15435_neg
  have he : Real.log (146558823529411 / 500000000000) = -Real.log (500000000000 / 146558823529411) := by
    rw [show ((146558823529411 / 500000000000) : ℝ) = ((500000000000 / 146558823529411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15436_neg : (5710527349 / 1000000000) ≤ -Real.log (31250000000 / 9438446969697) ∧
    -Real.log (31250000000 / 9438446969697) ≤ (2855263679 / 500000000) := by
  have h := checkLog_sound (w := (1438446969697 / 17438446969697)) (n := 12)
    (lo := (165349909 / 1000000000)) (hi := (16534991 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9438446969697 / 8000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(9438446969697 / 8000000000000) = 1/(31250000000 / 9438446969697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15436 : Bounds (5710527349 / 1000000000) (2855263679 / 500000000) (Real.log (9438446969697 / 31250000000)) := by
  have h := reflection_log_15436_neg
  have he : Real.log (9438446969697 / 31250000000) = -Real.log (31250000000 / 9438446969697) := by
    rw [show ((9438446969697 / 31250000000) : ℝ) = ((31250000000 / 9438446969697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15437_neg : (689942049 / 1000000000) ≤ -Real.log (625 / 1246) ∧
    -Real.log (625 / 1246) ≤ (13798841 / 20000000) := by
  have h := checkLog_sound (w := (621 / 1871)) (n := 12)
    (lo := (689942049 / 1000000000)) (hi := (13798841 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1246 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1246 / 625) = 1/(625 / 1246) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15437 : Bounds (689942049 / 1000000000) (13798841 / 20000000) (Real.log (1246 / 625)) := by
  have h := reflection_log_15437_neg
  have he : Real.log (1246 / 625) = -Real.log (625 / 1246) := by
    rw [show ((1246 / 625) : ℝ) = ((625 / 1246) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15438_neg : (1262864321 / 250000000) ≤ -Real.log (4 / 625) ∧
    -Real.log (4 / 625) ≤ (1262864323 / 250000000) := by
  have h := checkLog_sound (w := (113 / 1137)) (n := 12)
    (lo := (12464189 / 62500000)) (hi := (7977081 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 512) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 512) = 1/(4 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15438 : Bounds (-1262864323 / 250000000) (-1262864321 / 250000000) (Real.log (4 / 625)) := by
  have h := reflection_log_15438_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15439_neg : (496553 / 500000000) ≤ -Real.log (625000 / 625621) ∧
    -Real.log (625000 / 625621) ≤ (993107 / 1000000000) := by
  have h := checkLog_sound (w := (621 / 1250621)) (n := 12)
    (lo := (496553 / 500000000)) (hi := (993107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625621 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625621 / 625000) = 1/(625000 / 625621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15439 : Bounds (496553 / 500000000) (993107 / 1000000000) (Real.log (625621 / 625000)) := by
  have h := reflection_log_15439_neg
  have he : Real.log (625621 / 625000) = -Real.log (625000 / 625621) := by
    rw [show ((625621 / 625000) : ℝ) = ((625000 / 625621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15440_neg : (994093 / 1000000000) ≤ -Real.log (624379 / 625000) ∧
    -Real.log (624379 / 625000) ≤ (497047 / 500000000) := by
  have h := checkLog_sound (w := (621 / 1249379)) (n := 12)
    (lo := (994093 / 1000000000)) (hi := (497047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624379) = 1/(624379 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15440 : Bounds (-497047 / 500000000) (-994093 / 1000000000) (Real.log (624379 / 625000)) := by
  have h := reflection_log_15440_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15441_neg : (19953409 / 40000000) ≤ -Real.log (500000 / 823401) ∧
    -Real.log (500000 / 823401) ≤ (249417613 / 500000000) := by
  have h := checkLog_sound (w := (323401 / 1323401)) (n := 12)
    (lo := (19953409 / 40000000)) (hi := (249417613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((823401 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(823401 / 500000) = 1/(500000 / 823401) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15441 : Bounds (19953409 / 40000000) (249417613 / 500000000) (Real.log (823401 / 500000)) := by
  have h := reflection_log_15441_neg
  have he : Real.log (823401 / 500000) = -Real.log (500000 / 823401) := by
    rw [show ((823401 / 500000) : ℝ) = ((500000 / 823401) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15442_neg : (130090809 / 125000000) ≤ -Real.log (176599 / 500000) ∧
    -Real.log (176599 / 500000) ≤ (520363237 / 500000000) := by
  have h := checkLog_sound (w := (73401 / 426599)) (n := 12)
    (lo := (86894823 / 250000000)) (hi := (347579293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 176599) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 176599) = 1/(176599 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15442 : Bounds (-520363237 / 500000000) (-130090809 / 125000000) (Real.log (176599 / 500000)) := by
  have h := reflection_log_15442_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15443_neg : (99881173 / 200000000) ≤ -Real.log (500000 / 823871) ∧
    -Real.log (500000 / 823871) ≤ (249702933 / 500000000) := by
  have h := checkLog_sound (w := (323871 / 1323871)) (n := 12)
    (lo := (99881173 / 200000000)) (hi := (249702933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((823871 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(823871 / 500000) = 1/(500000 / 823871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15443 : Bounds (99881173 / 200000000) (249702933 / 500000000) (Real.log (823871 / 500000)) := by
  have h := reflection_log_15443_neg
  have he : Real.log (823871 / 500000) = -Real.log (500000 / 823871) := by
    rw [show ((823871 / 500000) : ℝ) = ((500000 / 823871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15444_neg : (130423927 / 125000000) ≤ -Real.log (176129 / 500000) ∧
    -Real.log (176129 / 500000) ≤ (521695709 / 500000000) := by
  have h := checkLog_sound (w := (73871 / 426129)) (n := 12)
    (lo := (87561059 / 250000000)) (hi := (350244237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 176129) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 176129) = 1/(176129 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15444 : Bounds (-521695709 / 500000000) (-130423927 / 125000000) (Real.log (176129 / 500000)) := by
  have h := reflection_log_15444_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15445_neg : (543985551 / 1000000000) ≤ -Real.log (145107575359 / 250000000000) ∧
    -Real.log (145107575359 / 250000000000) ≤ (33999097 / 62500000) := by
  have h := checkLog_sound (w := (104892424641 / 395107575359)) (n := 12)
    (lo := (543985551 / 1000000000)) (hi := (33999097 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 145107575359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 145107575359) = 1/(145107575359 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15445 : Bounds (-33999097 / 62500000) (-543985551 / 1000000000) (Real.log (145107575359 / 250000000000)) := by
  have h := reflection_log_15445_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15446_neg : (541891247 / 1000000000) ≤ -Real.log (145411793199 / 250000000000) ∧
    -Real.log (145411793199 / 250000000000) ≤ (33868203 / 62500000) := by
  have h := checkLog_sound (w := (104588206801 / 395411793199)) (n := 12)
    (lo := (541891247 / 1000000000)) (hi := (33868203 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 145411793199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 145411793199) = 1/(145411793199 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15446 : Bounds (-33868203 / 62500000) (-541891247 / 1000000000) (Real.log (145411793199 / 250000000000)) := by
  have h := reflection_log_15446_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15447_neg : (1539561697 / 1000000000) ≤ -Real.log (250000000000 / 1165636555133) ∧
    -Real.log (250000000000 / 1165636555133) ≤ (15395617 / 10000000) := by
  have h := checkLog_sound (w := (165636555133 / 2165636555133)) (n := 12)
    (lo := (153267337 / 1000000000)) (hi := (76633669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1165636555133 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1165636555133 / 1000000000000) = 1/(250000000000 / 1165636555133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15447 : Bounds (1539561697 / 1000000000) (15395617 / 10000000) (Real.log (1165636555133 / 250000000000)) := by
  have h := reflection_log_15447_neg
  have he : Real.log (1165636555133 / 250000000000) = -Real.log (250000000000 / 1165636555133) := by
    rw [show ((1165636555133 / 250000000000) : ℝ) = ((250000000000 / 1165636555133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15448_neg : (771398641 / 500000000) ≤ -Real.log (12500000000 / 58470708969) ∧
    -Real.log (12500000000 / 58470708969) ≤ (308559457 / 200000000) := by
  have h := checkLog_sound (w := (8470708969 / 108470708969)) (n := 12)
    (lo := (78251461 / 500000000)) (hi := (156502923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58470708969 / 50000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(58470708969 / 50000000000) = 1/(12500000000 / 58470708969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15448 : Bounds (771398641 / 500000000) (308559457 / 200000000) (Real.log (58470708969 / 12500000000)) := by
  have h := reflection_log_15448_neg
  have he : Real.log (58470708969 / 12500000000) = -Real.log (12500000000 / 58470708969) := by
    rw [show ((58470708969 / 12500000000) : ℝ) = ((12500000000 / 58470708969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15449_neg : (5710527349 / 1000000000) ≤ -Real.log (500000000000 / 151015151515151) ∧
    -Real.log (500000000000 / 151015151515151) ≤ (2855263679 / 500000000) := by
  have h := checkLog_sound (w := (23015151515151 / 279015151515151)) (n := 12)
    (lo := (165349909 / 1000000000)) (hi := (16534991 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151015151515151 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(151015151515151 / 128000000000000) = 1/(500000000000 / 151015151515151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15449 : Bounds (5710527349 / 1000000000) (2855263679 / 500000000) (Real.log (151015151515151 / 500000000000)) := by
  have h := reflection_log_15449_neg
  have he : Real.log (151015151515151 / 500000000000) = -Real.log (500000000000 / 151015151515151) := by
    rw [show ((151015151515151 / 500000000000) : ℝ) = ((500000000000 / 151015151515151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15450_neg : (5741399333 / 1000000000) ≤ -Real.log (2 / 623) ∧
    -Real.log (2 / 623) ≤ (2870699671 / 500000000) := by
  have h := checkLog_sound (w := (111 / 1135)) (n := 12)
    (lo := (196221893 / 1000000000)) (hi := (98110947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((623 / 512) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(623 / 512) = 1/(2 / 623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15450 : Bounds (5741399333 / 1000000000) (2870699671 / 500000000) (Real.log (623 / 2)) := by
  have h := reflection_log_15450_neg
  have he : Real.log (623 / 2) = -Real.log (2 / 623) := by
    rw [show ((623 / 2) : ℝ) = ((2 / 623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15451_neg : (138008473 / 200000000) ≤ -Real.log (5000 / 9969) ∧
    -Real.log (5000 / 9969) ≤ (345021183 / 500000000) := by
  have h := checkLog_sound (w := (4969 / 14969)) (n := 12)
    (lo := (138008473 / 200000000)) (hi := (345021183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9969 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9969 / 5000) = 1/(5000 / 9969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15451 : Bounds (138008473 / 200000000) (345021183 / 500000000) (Real.log (9969 / 5000)) := by
  have h := reflection_log_15451_neg
  have he : Real.log (9969 / 5000) = -Real.log (5000 / 9969) := by
    rw [show ((9969 / 5000) : ℝ) = ((5000 / 9969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15452_neg : (5083205983 / 1000000000) ≤ -Real.log (31 / 5000) ∧
    -Real.log (31 / 5000) ≤ (5083205991 / 1000000000) := by
  have h := checkLog_sound (w := (129 / 1121)) (n := 12)
    (lo := (231175723 / 1000000000)) (hi := (57793931 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 496) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 496) = 1/(31 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15452 : Bounds (-5083205991 / 1000000000) (-5083205983 / 1000000000) (Real.log (31 / 5000)) := by
  have h := reflection_log_15452_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15453_neg : (496653 / 500000000) ≤ -Real.log (5000000 / 5004969) ∧
    -Real.log (5000000 / 5004969) ≤ (993307 / 1000000000) := by
  have h := checkLog_sound (w := (4969 / 10004969)) (n := 12)
    (lo := (496653 / 500000000)) (hi := (993307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004969 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004969 / 5000000) = 1/(5000000 / 5004969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15453 : Bounds (496653 / 500000000) (993307 / 1000000000) (Real.log (5004969 / 5000000)) := by
  have h := reflection_log_15453_neg
  have he : Real.log (5004969 / 5000000) = -Real.log (5000000 / 5004969) := by
    rw [show ((5004969 / 5000000) : ℝ) = ((5000000 / 5004969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15454_neg : (497147 / 500000000) ≤ -Real.log (4995031 / 5000000) ∧
    -Real.log (4995031 / 5000000) ≤ (198859 / 200000000) := by
  have h := checkLog_sound (w := (4969 / 9995031)) (n := 12)
    (lo := (497147 / 500000000)) (hi := (198859 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995031) = 1/(4995031 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15454 : Bounds (-198859 / 200000000) (-497147 / 500000000) (Real.log (4995031 / 5000000)) := by
  have h := reflection_log_15454_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15455_neg : (499025879 / 1000000000) ≤ -Real.log (250000 / 411779) ∧
    -Real.log (250000 / 411779) ≤ (12475647 / 25000000) := by
  have h := checkLog_sound (w := (161779 / 661779)) (n := 12)
    (lo := (499025879 / 1000000000)) (hi := (12475647 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((411779 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(411779 / 250000) = 1/(250000 / 411779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15455 : Bounds (499025879 / 1000000000) (12475647 / 25000000) (Real.log (411779 / 250000)) := by
  have h := reflection_log_15455_neg
  have he : Real.log (411779 / 250000) = -Real.log (250000 / 411779) := by
    rw [show ((411779 / 250000) : ℝ) = ((250000 / 411779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15456_neg : (1041615887 / 1000000000) ≤ -Real.log (88221 / 250000) ∧
    -Real.log (88221 / 250000) ≤ (1041615889 / 1000000000) := by
  have h := checkLog_sound (w := (36779 / 213221)) (n := 12)
    (lo := (348468707 / 1000000000)) (hi := (87117177 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88221) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 88221) = 1/(88221 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15456 : Bounds (-1041615889 / 1000000000) (-1041615887 / 1000000000) (Real.log (88221 / 250000)) := by
  have h := reflection_log_15456_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15457_neg : (249798509 / 500000000) ≤ -Real.log (1000000 / 1648057) ∧
    -Real.log (1000000 / 1648057) ≤ (499597019 / 1000000000) := by
  have h := checkLog_sound (w := (648057 / 2648057)) (n := 12)
    (lo := (249798509 / 500000000)) (hi := (499597019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1648057 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1648057 / 1000000) = 1/(1000000 / 1648057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15457 : Bounds (249798509 / 500000000) (499597019 / 1000000000) (Real.log (1648057 / 1000000)) := by
  have h := reflection_log_15457_neg
  have he : Real.log (1648057 / 1000000) = -Real.log (1000000 / 1648057) := by
    rw [show ((1648057 / 1000000) : ℝ) = ((1000000 / 1648057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15458_neg : (1044286047 / 1000000000) ≤ -Real.log (351943 / 1000000) ∧
    -Real.log (351943 / 1000000) ≤ (1044286049 / 1000000000) := by
  have h := checkLog_sound (w := (148057 / 851943)) (n := 12)
    (lo := (351138867 / 1000000000)) (hi := (87784717 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 351943) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 351943) = 1/(351943 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15458 : Bounds (-1044286049 / 1000000000) (-1044286047 / 1000000000) (Real.log (351943 / 1000000)) := by
  have h := reflection_log_15458_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15459_neg : (54468903 / 100000000) ≤ -Real.log (580022124751 / 1000000000000) ∧
    -Real.log (580022124751 / 1000000000000) ≤ (544689031 / 1000000000) := by
  have h := checkLog_sound (w := (419977875249 / 1580022124751)) (n := 12)
    (lo := (54468903 / 100000000)) (hi := (544689031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 580022124751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 580022124751) = 1/(580022124751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15459 : Bounds (-544689031 / 1000000000) (-54468903 / 100000000) (Real.log (580022124751 / 1000000000000)) := by
  have h := reflection_log_15459_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15460_neg : (67823751 / 125000000) ≤ -Real.log (36327555159 / 62500000000) ∧
    -Real.log (36327555159 / 62500000000) ≤ (542590009 / 1000000000) := by
  have h := checkLog_sound (w := (26172444841 / 98827555159)) (n := 12)
    (lo := (67823751 / 125000000)) (hi := (542590009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 36327555159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 36327555159) = 1/(36327555159 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15460 : Bounds (-542590009 / 1000000000) (-67823751 / 125000000) (Real.log (36327555159 / 62500000000)) := by
  have h := reflection_log_15460_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15461_neg : (770320883 / 500000000) ≤ -Real.log (500000000000 / 2333792407703) ∧
    -Real.log (500000000000 / 2333792407703) ≤ (1540641769 / 1000000000) := by
  have h := checkLog_sound (w := (333792407703 / 4333792407703)) (n := 12)
    (lo := (77173703 / 500000000)) (hi := (154347407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2333792407703 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2333792407703 / 2000000000000) = 1/(500000000000 / 2333792407703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15461 : Bounds (770320883 / 500000000) (1540641769 / 1000000000) (Real.log (2333792407703 / 500000000000)) := by
  have h := reflection_log_15461_neg
  have he : Real.log (2333792407703 / 500000000000) = -Real.log (500000000000 / 2333792407703) := by
    rw [show ((2333792407703 / 500000000000) : ℝ) = ((500000000000 / 2333792407703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15462_neg : (308776613 / 200000000) ≤ -Real.log (50000000000 / 234136919899) ∧
    -Real.log (50000000000 / 234136919899) ≤ (385970767 / 250000000) := by
  have h := checkLog_sound (w := (34136919899 / 434136919899)) (n := 12)
    (lo := (31517741 / 200000000)) (hi := (78794353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((234136919899 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(234136919899 / 200000000000) = 1/(50000000000 / 234136919899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15462 : Bounds (308776613 / 200000000) (385970767 / 250000000) (Real.log (234136919899 / 50000000000)) := by
  have h := reflection_log_15462_neg
  have he : Real.log (234136919899 / 50000000000) = -Real.log (50000000000 / 234136919899) := by
    rw [show ((234136919899 / 50000000000) : ℝ) = ((50000000000 / 234136919899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15463_neg : (1443312087 / 250000000) ≤ -Real.log (250000000000 / 80395161290323) ∧
    -Real.log (250000000000 / 80395161290323) ≤ (5773248357 / 1000000000) := by
  have h := checkLog_sound (w := (16395161290323 / 144395161290323)) (n := 12)
    (lo := (57017727 / 250000000)) (hi := (228070909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80395161290323 / 64000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(80395161290323 / 64000000000000) = 1/(250000000000 / 80395161290323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15463 : Bounds (1443312087 / 250000000) (5773248357 / 1000000000) (Real.log (80395161290323 / 250000000000)) := by
  have h := reflection_log_15463_neg
  have he : Real.log (80395161290323 / 250000000000) = -Real.log (250000000000 / 80395161290323) := by
    rw [show ((80395161290323 / 250000000000) : ℝ) = ((250000000000 / 80395161290323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15464_neg : (690142671 / 1000000000) ≤ -Real.log (500 / 997) ∧
    -Real.log (500 / 997) ≤ (43133917 / 62500000) := by
  have h := checkLog_sound (w := (497 / 1497)) (n := 12)
    (lo := (690142671 / 1000000000)) (hi := (43133917 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((997 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(997 / 500) = 1/(500 / 997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15464 : Bounds (690142671 / 1000000000) (43133917 / 62500000) (Real.log (997 / 500)) := by
  have h := reflection_log_15464_neg
  have he : Real.log (997 / 500) = -Real.log (500 / 997) := by
    rw [show ((997 / 500) : ℝ) = ((500 / 997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15465_neg : (1023199161 / 200000000) ≤ -Real.log (3 / 500) ∧
    -Real.log (3 / 500) ≤ (5115995813 / 1000000000) := by
  have h := checkLog_sound (w := (29 / 221)) (n := 12)
    (lo := (52793109 / 200000000)) (hi := (131982773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 96) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(125 / 96) = 1/(3 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15465 : Bounds (-5115995813 / 1000000000) (-1023199161 / 200000000) (Real.log (3 / 500)) := by
  have h := reflection_log_15465_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15466_neg : (496753 / 500000000) ≤ -Real.log (500000 / 500497) ∧
    -Real.log (500000 / 500497) ≤ (993507 / 1000000000) := by
  have h := checkLog_sound (w := (497 / 1000497)) (n := 12)
    (lo := (496753 / 500000000)) (hi := (993507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500497 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500497 / 500000) = 1/(500000 / 500497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15466 : Bounds (496753 / 500000000) (993507 / 1000000000) (Real.log (500497 / 500000)) := by
  have h := reflection_log_15466_neg
  have he : Real.log (500497 / 500000) = -Real.log (500000 / 500497) := by
    rw [show ((500497 / 500000) : ℝ) = ((500000 / 500497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15467_neg : (497247 / 500000000) ≤ -Real.log (499503 / 500000) ∧
    -Real.log (499503 / 500000) ≤ (198899 / 200000000) := by
  have h := checkLog_sound (w := (497 / 999503)) (n := 12)
    (lo := (497247 / 500000000)) (hi := (198899 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499503) = 1/(499503 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15467 : Bounds (-198899 / 200000000) (-497247 / 500000000) (Real.log (499503 / 500000)) := by
  have h := reflection_log_15467_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15468_neg : (499216497 / 1000000000) ≤ -Real.log (100000 / 164743) ∧
    -Real.log (100000 / 164743) ≤ (249608249 / 500000000) := by
  have h := checkLog_sound (w := (64743 / 264743)) (n := 12)
    (lo := (499216497 / 1000000000)) (hi := (249608249 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164743 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164743 / 100000) = 1/(100000 / 164743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15468 : Bounds (499216497 / 1000000000) (249608249 / 500000000) (Real.log (164743 / 100000)) := by
  have h := reflection_log_15468_neg
  have he : Real.log (164743 / 100000) = -Real.log (100000 / 164743) := by
    rw [show ((164743 / 100000) : ℝ) = ((100000 / 164743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15469_neg : (521253047 / 500000000) ≤ -Real.log (35257 / 100000) ∧
    -Real.log (35257 / 100000) ≤ (65156631 / 62500000) := by
  have h := checkLog_sound (w := (14743 / 85257)) (n := 12)
    (lo := (174679457 / 500000000)) (hi := (69871783 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35257) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 35257) = 1/(35257 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15469 : Bounds (-65156631 / 62500000) (-521253047 / 500000000) (Real.log (35257 / 100000)) := by
  have h := reflection_log_15469_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15470_neg : (24989437 / 50000000) ≤ -Real.log (1000000 / 1648373) ∧
    -Real.log (1000000 / 1648373) ≤ (499788741 / 1000000000) := by
  have h := checkLog_sound (w := (648373 / 2648373)) (n := 12)
    (lo := (24989437 / 50000000)) (hi := (499788741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1648373 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1648373 / 1000000) = 1/(1000000 / 1648373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15470 : Bounds (24989437 / 50000000) (499788741 / 1000000000) (Real.log (1648373 / 1000000)) := by
  have h := reflection_log_15470_neg
  have he : Real.log (1648373 / 1000000) = -Real.log (1000000 / 1648373) := by
    rw [show ((1648373 / 1000000) : ℝ) = ((1000000 / 1648373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15471_neg : (1045184323 / 1000000000) ≤ -Real.log (351627 / 1000000) ∧
    -Real.log (351627 / 1000000) ≤ (41807373 / 40000000) := by
  have h := checkLog_sound (w := (148373 / 851627)) (n := 12)
    (lo := (352037143 / 1000000000)) (hi := (44004643 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 351627) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 351627) = 1/(351627 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15471 : Bounds (-41807373 / 40000000) (-1045184323 / 1000000000) (Real.log (351627 / 1000000)) := by
  have h := reflection_log_15471_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15472_neg : (545395583 / 1000000000) ≤ -Real.log (579612452871 / 1000000000000) ∧
    -Real.log (579612452871 / 1000000000000) ≤ (4260903 / 7812500) := by
  have h := checkLog_sound (w := (420387547129 / 1579612452871)) (n := 12)
    (lo := (545395583 / 1000000000)) (hi := (4260903 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 579612452871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 579612452871) = 1/(579612452871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15472 : Bounds (-4260903 / 7812500) (-545395583 / 1000000000) (Real.log (579612452871 / 1000000000000)) := by
  have h := reflection_log_15472_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15473_neg : (543289597 / 1000000000) ≤ -Real.log (5808343951 / 10000000000) ∧
    -Real.log (5808343951 / 10000000000) ≤ (271644799 / 500000000) := by
  have h := checkLog_sound (w := (4191656049 / 15808343951)) (n := 12)
    (lo := (543289597 / 1000000000)) (hi := (271644799 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 5808343951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 5808343951) = 1/(5808343951 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15473 : Bounds (-271644799 / 500000000) (-543289597 / 1000000000) (Real.log (5808343951 / 10000000000)) := by
  have h := reflection_log_15473_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15474_neg : (1541722591 / 1000000000) ≤ -Real.log (500000000000 / 2336316192529) ∧
    -Real.log (500000000000 / 2336316192529) ≤ (770861297 / 500000000) := by
  have h := checkLog_sound (w := (336316192529 / 4336316192529)) (n := 12)
    (lo := (155428231 / 1000000000)) (hi := (19428529 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2336316192529 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2336316192529 / 2000000000000) = 1/(500000000000 / 2336316192529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15474 : Bounds (1541722591 / 1000000000) (770861297 / 500000000) (Real.log (2336316192529 / 500000000000)) := by
  have h := reflection_log_15474_neg
  have he : Real.log (2336316192529 / 500000000000) = -Real.log (500000000000 / 2336316192529) := by
    rw [show ((2336316192529 / 500000000000) : ℝ) = ((500000000000 / 2336316192529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15475_neg : (193121633 / 125000000) ≤ -Real.log (500000000000 / 2343922679431) ∧
    -Real.log (500000000000 / 2343922679431) ≤ (1544973067 / 1000000000) := by
  have h := checkLog_sound (w := (343922679431 / 4343922679431)) (n := 12)
    (lo := (9917419 / 62500000)) (hi := (31735741 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2343922679431 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2343922679431 / 2000000000000) = 1/(500000000000 / 2343922679431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15475 : Bounds (193121633 / 125000000) (1544973067 / 1000000000) (Real.log (2343922679431 / 500000000000)) := by
  have h := reflection_log_15475_neg
  have he : Real.log (2343922679431 / 500000000000) = -Real.log (500000000000 / 2343922679431) := by
    rw [show ((2343922679431 / 500000000000) : ℝ) = ((500000000000 / 2343922679431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15476_neg : (1443312087 / 250000000) ≤ -Real.log (100000000000 / 32158064516129) ∧
    -Real.log (100000000000 / 32158064516129) ≤ (5773248357 / 1000000000) := by
  have h := checkLog_sound (w := (6558064516129 / 57758064516129)) (n := 12)
    (lo := (57017727 / 250000000)) (hi := (228070909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32158064516129 / 25600000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(32158064516129 / 25600000000000) = 1/(100000000000 / 32158064516129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15476 : Bounds (1443312087 / 250000000) (5773248357 / 1000000000) (Real.log (32158064516129 / 100000000000)) := by
  have h := reflection_log_15476_neg
  have he : Real.log (32158064516129 / 100000000000) = -Real.log (100000000000 / 32158064516129) := by
    rw [show ((32158064516129 / 100000000000) : ℝ) = ((100000000000 / 32158064516129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15477_neg : (1451534619 / 250000000) ≤ -Real.log (500000000000 / 166166666666667) ∧
    -Real.log (500000000000 / 166166666666667) ≤ (1161227697 / 200000000) := by
  have h := checkLog_sound (w := (38166666666667 / 294166666666667)) (n := 12)
    (lo := (65240259 / 250000000)) (hi := (260961037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166166666666667 / 128000000000000) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(166166666666667 / 128000000000000) = 1/(500000000000 / 166166666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15477 : Bounds (1451534619 / 250000000) (1161227697 / 200000000) (Real.log (166166666666667 / 500000000000)) := by
  have h := reflection_log_15477_neg
  have he : Real.log (166166666666667 / 500000000000) = -Real.log (500000000000 / 166166666666667) := by
    rw [show ((166166666666667 / 500000000000) : ℝ) = ((500000000000 / 166166666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15478_neg : (690242967 / 1000000000) ≤ -Real.log (5000 / 9971) ∧
    -Real.log (5000 / 9971) ≤ (86280371 / 125000000) := by
  have h := checkLog_sound (w := (4971 / 14971)) (n := 12)
    (lo := (690242967 / 1000000000)) (hi := (86280371 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9971 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9971 / 5000) = 1/(5000 / 9971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15478 : Bounds (690242967 / 1000000000) (86280371 / 125000000) (Real.log (9971 / 5000)) := by
  have h := reflection_log_15478_neg
  have he : Real.log (9971 / 5000) = -Real.log (5000 / 9971) := by
    rw [show ((9971 / 5000) : ℝ) = ((5000 / 9971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15479_neg : (5149897357 / 1000000000) ≤ -Real.log (29 / 5000) ∧
    -Real.log (29 / 5000) ≤ (1029979473 / 200000000) := by
  have h := checkLog_sound (w := (161 / 1089)) (n := 12)
    (lo := (297867097 / 1000000000)) (hi := (148933549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 464) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(625 / 464) = 1/(29 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15479 : Bounds (-1029979473 / 200000000) (-5149897357 / 1000000000) (Real.log (29 / 5000)) := by
  have h := reflection_log_15479_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15480_neg : (496853 / 500000000) ≤ -Real.log (5000000 / 5004971) ∧
    -Real.log (5000000 / 5004971) ≤ (993707 / 1000000000) := by
  have h := checkLog_sound (w := (4971 / 10004971)) (n := 12)
    (lo := (496853 / 500000000)) (hi := (993707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004971 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004971 / 5000000) = 1/(5000000 / 5004971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15480 : Bounds (496853 / 500000000) (993707 / 1000000000) (Real.log (5004971 / 5000000)) := by
  have h := reflection_log_15480_neg
  have he : Real.log (5004971 / 5000000) = -Real.log (5000000 / 5004971) := by
    rw [show ((5004971 / 5000000) : ℝ) = ((5000000 / 5004971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15481_neg : (497347 / 500000000) ≤ -Real.log (4995029 / 5000000) ∧
    -Real.log (4995029 / 5000000) ≤ (198939 / 200000000) := by
  have h := checkLog_sound (w := (4971 / 9995029)) (n := 12)
    (lo := (497347 / 500000000)) (hi := (198939 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995029) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995029) = 1/(4995029 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15481 : Bounds (-198939 / 200000000) (-497347 / 500000000) (Real.log (4995029 / 5000000)) := by
  have h := reflection_log_15481_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15482_neg : (4994089 / 10000000) ≤ -Real.log (1000000 / 1647747) ∧
    -Real.log (1000000 / 1647747) ≤ (499408901 / 1000000000) := by
  have h := checkLog_sound (w := (647747 / 2647747)) (n := 12)
    (lo := (4994089 / 10000000)) (hi := (499408901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1647747 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1647747 / 1000000) = 1/(1000000 / 1647747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15482 : Bounds (4994089 / 10000000) (499408901 / 1000000000) (Real.log (1647747 / 1000000)) := by
  have h := reflection_log_15482_neg
  have he : Real.log (1647747 / 1000000) = -Real.log (1000000 / 1647747) := by
    rw [show ((1647747 / 1000000) : ℝ) = ((1000000 / 1647747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15483_neg : (1043405611 / 1000000000) ≤ -Real.log (352253 / 1000000) ∧
    -Real.log (352253 / 1000000) ≤ (1043405613 / 1000000000) := by
  have h := checkLog_sound (w := (147747 / 852253)) (n := 12)
    (lo := (350258431 / 1000000000)) (hi := (1368197 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 352253) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 352253) = 1/(352253 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15483 : Bounds (-1043405613 / 1000000000) (-1043405611 / 1000000000) (Real.log (352253 / 1000000)) := by
  have h := reflection_log_15483_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15484_neg : (499981033 / 1000000000) ≤ -Real.log (100000 / 164869) ∧
    -Real.log (100000 / 164869) ≤ (249990517 / 500000000) := by
  have h := checkLog_sound (w := (64869 / 264869)) (n := 12)
    (lo := (499981033 / 1000000000)) (hi := (249990517 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164869 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164869 / 100000) = 1/(100000 / 164869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15484 : Bounds (499981033 / 1000000000) (249990517 / 500000000) (Real.log (164869 / 100000)) := by
  have h := reflection_log_15484_neg
  have he : Real.log (164869 / 100000) = -Real.log (100000 / 164869) := by
    rw [show ((164869 / 100000) : ℝ) = ((100000 / 164869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15485_neg : (1046086253 / 1000000000) ≤ -Real.log (35131 / 100000) ∧
    -Real.log (35131 / 100000) ≤ (209217251 / 200000000) := by
  have h := checkLog_sound (w := (14869 / 85131)) (n := 12)
    (lo := (352939073 / 1000000000)) (hi := (176469537 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35131) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 35131) = 1/(35131 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15485 : Bounds (-209217251 / 200000000) (-1046086253 / 1000000000) (Real.log (35131 / 100000)) := by
  have h := reflection_log_15485_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15486_neg : (546105221 / 1000000000) ≤ -Real.log (5792012839 / 10000000000) ∧
    -Real.log (5792012839 / 10000000000) ≤ (273052611 / 500000000) := by
  have h := checkLog_sound (w := (4207987161 / 15792012839)) (n := 12)
    (lo := (546105221 / 1000000000)) (hi := (273052611 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 5792012839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 5792012839) = 1/(5792012839 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15486 : Bounds (-273052611 / 500000000) (-546105221 / 1000000000) (Real.log (5792012839 / 10000000000)) := by
  have h := reflection_log_15486_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15487_neg : (543996711 / 1000000000) ≤ -Real.log (580423823991 / 1000000000000) ∧
    -Real.log (580423823991 / 1000000000000) ≤ (67999589 / 125000000) := by
  have h := checkLog_sound (w := (419576176009 / 1580423823991)) (n := 12)
    (lo := (543996711 / 1000000000)) (hi := (67999589 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 580423823991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 580423823991) = 1/(580423823991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15487 : Bounds (-67999589 / 125000000) (-543996711 / 1000000000) (Real.log (580423823991 / 1000000000000)) := by
  have h := reflection_log_15487_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
