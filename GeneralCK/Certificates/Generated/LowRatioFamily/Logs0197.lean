import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_12608_neg : (207707719 / 500000000) ≤ -Real.log (200 / 303) ∧
    -Real.log (200 / 303) ≤ (415415439 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 503)) (n := 12)
    (lo := (207707719 / 500000000)) (hi := (415415439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303 / 200) = 1/(200 / 303) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12608 : Bounds (207707719 / 500000000) (415415439 / 1000000000) (Real.log (303 / 200)) := by
  have h := reflection_log_12608_neg
  have he : Real.log (303 / 200) = -Real.log (200 / 303) := by
    rw [show ((303 / 200) : ℝ) = ((200 / 303) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12609_neg : (723606387 / 1000000000) ≤ -Real.log (97 / 200) ∧
    -Real.log (97 / 200) ≤ (723606389 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 197)) (n := 12)
    (lo := (30459207 / 1000000000)) (hi := (3807401 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 97) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100 / 97) = 1/(97 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12609 : Bounds (-723606389 / 1000000000) (-723606387 / 1000000000) (Real.log (97 / 200)) := by
  have h := reflection_log_12609_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12610_neg : (514867 / 1000000000) ≤ -Real.log (200000 / 200103) ∧
    -Real.log (200000 / 200103) ≤ (128717 / 250000000) := by
  have h := checkLog_sound (w := (103 / 400103)) (n := 12)
    (lo := (514867 / 1000000000)) (hi := (128717 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200103 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200103 / 200000) = 1/(200000 / 200103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12610 : Bounds (514867 / 1000000000) (128717 / 250000000) (Real.log (200103 / 200000)) := by
  have h := reflection_log_12610_neg
  have he : Real.log (200103 / 200000) = -Real.log (200000 / 200103) := by
    rw [show ((200103 / 200000) : ℝ) = ((200000 / 200103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12611_neg : (128783 / 250000000) ≤ -Real.log (199897 / 200000) ∧
    -Real.log (199897 / 200000) ≤ (515133 / 1000000000) := by
  have h := checkLog_sound (w := (103 / 399897)) (n := 12)
    (lo := (128783 / 250000000)) (hi := (515133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199897) = 1/(199897 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12611 : Bounds (-515133 / 1000000000) (-128783 / 250000000) (Real.log (199897 / 200000)) := by
  have h := reflection_log_12611_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12612_neg : (29769783 / 125000000) ≤ -Real.log (100000 / 126891) ∧
    -Real.log (100000 / 126891) ≤ (47631653 / 200000000) := by
  have h := checkLog_sound (w := (26891 / 226891)) (n := 12)
    (lo := (29769783 / 125000000)) (hi := (47631653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((126891 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(126891 / 100000) = 1/(100000 / 126891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12612 : Bounds (29769783 / 125000000) (47631653 / 200000000) (Real.log (126891 / 100000)) := by
  have h := reflection_log_12612_neg
  have he : Real.log (126891 / 100000) = -Real.log (100000 / 126891) := by
    rw [show ((126891 / 100000) : ℝ) = ((100000 / 126891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12613_neg : (313218707 / 1000000000) ≤ -Real.log (73109 / 100000) ∧
    -Real.log (73109 / 100000) ≤ (78304677 / 250000000) := by
  have h := checkLog_sound (w := (26891 / 173109)) (n := 12)
    (lo := (313218707 / 1000000000)) (hi := (78304677 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 73109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 73109) = 1/(73109 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12613 : Bounds (-78304677 / 250000000) (-313218707 / 1000000000) (Real.log (73109 / 100000)) := by
  have h := reflection_log_12613_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12614_neg : (239915709 / 1000000000) ≤ -Real.log (500000 / 635571) ∧
    -Real.log (500000 / 635571) ≤ (23991571 / 100000000) := by
  have h := checkLog_sound (w := (135571 / 1135571)) (n := 12)
    (lo := (239915709 / 1000000000)) (hi := (23991571 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((635571 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(635571 / 500000) = 1/(500000 / 635571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12614 : Bounds (239915709 / 1000000000) (23991571 / 100000000) (Real.log (635571 / 500000)) := by
  have h := reflection_log_12614_neg
  have he : Real.log (635571 / 500000) = -Real.log (500000 / 635571) := by
    rw [show ((635571 / 500000) : ℝ) = ((500000 / 635571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12615_neg : (316276353 / 1000000000) ≤ -Real.log (364429 / 500000) ∧
    -Real.log (364429 / 500000) ≤ (158138177 / 500000000) := by
  have h := checkLog_sound (w := (135571 / 864429)) (n := 12)
    (lo := (316276353 / 1000000000)) (hi := (158138177 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 364429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 364429) = 1/(364429 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12615 : Bounds (-158138177 / 500000000) (-316276353 / 1000000000) (Real.log (364429 / 500000)) := by
  have h := reflection_log_12615_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12616_neg : (19090161 / 250000000) ≤ -Real.log (231620503959 / 250000000000) ∧
    -Real.log (231620503959 / 250000000000) ≤ (15272129 / 200000000) := by
  have h := checkLog_sound (w := (18379496041 / 481620503959)) (n := 12)
    (lo := (19090161 / 250000000)) (hi := (15272129 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 231620503959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 231620503959) = 1/(231620503959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12616 : Bounds (-15272129 / 200000000) (-19090161 / 250000000) (Real.log (231620503959 / 250000000000)) := by
  have h := reflection_log_12616_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12617_neg : (75060443 / 1000000000) ≤ -Real.log (9276874119 / 10000000000) ∧
    -Real.log (9276874119 / 10000000000) ≤ (18765111 / 250000000) := by
  have h := checkLog_sound (w := (723125881 / 19276874119)) (n := 12)
    (lo := (75060443 / 1000000000)) (hi := (18765111 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9276874119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9276874119) = 1/(9276874119 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12617 : Bounds (-18765111 / 250000000) (-75060443 / 1000000000) (Real.log (9276874119 / 10000000000)) := by
  have h := reflection_log_12617_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12618_neg : (137844243 / 250000000) ≤ -Real.log (125000000000 / 216955162839) ∧
    -Real.log (125000000000 / 216955162839) ≤ (551376973 / 1000000000) := by
  have h := checkLog_sound (w := (91955162839 / 341955162839)) (n := 12)
    (lo := (137844243 / 250000000)) (hi := (551376973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216955162839 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216955162839 / 125000000000) = 1/(125000000000 / 216955162839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12618 : Bounds (137844243 / 250000000) (551376973 / 1000000000) (Real.log (216955162839 / 125000000000)) := by
  have h := reflection_log_12618_neg
  have he : Real.log (216955162839 / 125000000000) = -Real.log (125000000000 / 216955162839) := by
    rw [show ((216955162839 / 125000000000) : ℝ) = ((125000000000 / 216955162839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12619_neg : (278096031 / 500000000) ≤ -Real.log (15625000000 / 27250292581) ∧
    -Real.log (15625000000 / 27250292581) ≤ (556192063 / 1000000000) := by
  have h := checkLog_sound (w := (11625292581 / 42875292581)) (n := 12)
    (lo := (278096031 / 500000000)) (hi := (556192063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27250292581 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27250292581 / 15625000000) = 1/(15625000000 / 27250292581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12619 : Bounds (278096031 / 500000000) (556192063 / 1000000000) (Real.log (27250292581 / 15625000000)) := by
  have h := reflection_log_12619_neg
  have he : Real.log (27250292581 / 15625000000) = -Real.log (15625000000 / 27250292581) := by
    rw [show ((27250292581 / 15625000000) : ℝ) = ((15625000000 / 27250292581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12620_neg : (22617463 / 20000000) ≤ -Real.log (125000000000 / 387295081967) ∧
    -Real.log (125000000000 / 387295081967) ≤ (17669893 / 15625000) := by
  have h := checkLog_sound (w := (137295081967 / 637295081967)) (n := 12)
    (lo := (43772597 / 100000000)) (hi := (437725971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((387295081967 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(387295081967 / 250000000000) = 1/(125000000000 / 387295081967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12620 : Bounds (22617463 / 20000000) (17669893 / 15625000) (Real.log (387295081967 / 125000000000)) := by
  have h := reflection_log_12620_neg
  have he : Real.log (387295081967 / 125000000000) = -Real.log (125000000000 / 387295081967) := by
    rw [show ((387295081967 / 125000000000) : ℝ) = ((125000000000 / 387295081967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12621_neg : (569510913 / 500000000) ≤ -Real.log (62500000000 / 195231958763) ∧
    -Real.log (62500000000 / 195231958763) ≤ (284755457 / 250000000) := by
  have h := checkLog_sound (w := (70231958763 / 320231958763)) (n := 12)
    (lo := (222937323 / 500000000)) (hi := (445874647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((195231958763 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(195231958763 / 125000000000) = 1/(62500000000 / 195231958763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12621 : Bounds (569510913 / 500000000) (284755457 / 250000000) (Real.log (195231958763 / 62500000000)) := by
  have h := reflection_log_12621_neg
  have he : Real.log (195231958763 / 62500000000) = -Real.log (62500000000 / 195231958763) := by
    rw [show ((195231958763 / 62500000000) : ℝ) = ((62500000000 / 195231958763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12622_neg : (208696839 / 500000000) ≤ -Real.log (500 / 759) ∧
    -Real.log (500 / 759) ≤ (417393679 / 1000000000) := by
  have h := checkLog_sound (w := (259 / 1259)) (n := 12)
    (lo := (208696839 / 500000000)) (hi := (417393679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((759 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(759 / 500) = 1/(500 / 759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12622 : Bounds (208696839 / 500000000) (417393679 / 1000000000) (Real.log (759 / 500)) := by
  have h := reflection_log_12622_neg
  have he : Real.log (759 / 500) = -Real.log (500 / 759) := by
    rw [show ((759 / 500) : ℝ) = ((500 / 759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12623_neg : (182452791 / 250000000) ≤ -Real.log (241 / 500) ∧
    -Real.log (241 / 500) ≤ (364905583 / 500000000) := by
  have h := checkLog_sound (w := (9 / 491)) (n := 12)
    (lo := (2291499 / 62500000)) (hi := (7332797 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 241) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 241) = 1/(241 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12623 : Bounds (-364905583 / 500000000) (-182452791 / 250000000) (Real.log (241 / 500)) := by
  have h := reflection_log_12623_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12624_neg : (103573 / 200000000) ≤ -Real.log (500000 / 500259) ∧
    -Real.log (500000 / 500259) ≤ (258933 / 500000000) := by
  have h := checkLog_sound (w := (259 / 1000259)) (n := 12)
    (lo := (103573 / 200000000)) (hi := (258933 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500259 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500259 / 500000) = 1/(500000 / 500259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12624 : Bounds (103573 / 200000000) (258933 / 500000000) (Real.log (500259 / 500000)) := by
  have h := reflection_log_12624_neg
  have he : Real.log (500259 / 500000) = -Real.log (500000 / 500259) := by
    rw [show ((500259 / 500000) : ℝ) = ((500000 / 500259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12625_neg : (259067 / 500000000) ≤ -Real.log (499741 / 500000) ∧
    -Real.log (499741 / 500000) ≤ (103627 / 200000000) := by
  have h := checkLog_sound (w := (259 / 999741)) (n := 12)
    (lo := (259067 / 500000000)) (hi := (103627 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499741) = 1/(499741 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12625 : Bounds (-103627 / 200000000) (-259067 / 500000000) (Real.log (499741 / 500000)) := by
  have h := reflection_log_12625_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12626_neg : (47906503 / 200000000) ≤ -Real.log (200000 / 254131) ∧
    -Real.log (200000 / 254131) ≤ (59883129 / 250000000) := by
  have h := checkLog_sound (w := (54131 / 454131)) (n := 12)
    (lo := (47906503 / 200000000)) (hi := (59883129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((254131 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(254131 / 200000) = 1/(200000 / 254131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12626 : Bounds (47906503 / 200000000) (59883129 / 250000000) (Real.log (254131 / 200000)) := by
  have h := reflection_log_12626_neg
  have he : Real.log (254131 / 200000) = -Real.log (200000 / 254131) := by
    rw [show ((254131 / 200000) : ℝ) = ((200000 / 254131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12627_neg : (315608407 / 1000000000) ≤ -Real.log (145869 / 200000) ∧
    -Real.log (145869 / 200000) ≤ (39451051 / 125000000) := by
  have h := checkLog_sound (w := (54131 / 345869)) (n := 12)
    (lo := (315608407 / 1000000000)) (hi := (39451051 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 145869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 145869) = 1/(145869 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12627 : Bounds (-39451051 / 125000000) (-315608407 / 1000000000) (Real.log (145869 / 200000)) := by
  have h := reflection_log_12627_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12628_neg : (30161631 / 125000000) ≤ -Real.log (500000 / 636447) ∧
    -Real.log (500000 / 636447) ≤ (241293049 / 1000000000) := by
  have h := checkLog_sound (w := (136447 / 1136447)) (n := 12)
    (lo := (30161631 / 125000000)) (hi := (241293049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((636447 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(636447 / 500000) = 1/(500000 / 636447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12628 : Bounds (30161631 / 125000000) (241293049 / 1000000000) (Real.log (636447 / 500000)) := by
  have h := reflection_log_12628_neg
  have he : Real.log (636447 / 500000) = -Real.log (500000 / 636447) := by
    rw [show ((636447 / 500000) : ℝ) = ((500000 / 636447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12629_neg : (318683007 / 1000000000) ≤ -Real.log (363553 / 500000) ∧
    -Real.log (363553 / 500000) ≤ (2489711 / 7812500) := by
  have h := checkLog_sound (w := (136447 / 863553)) (n := 12)
    (lo := (318683007 / 1000000000)) (hi := (2489711 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 363553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 363553) = 1/(363553 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12629 : Bounds (-2489711 / 7812500) (-318683007 / 1000000000) (Real.log (363553 / 500000)) := by
  have h := reflection_log_12629_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12630_neg : (77389959 / 1000000000) ≤ -Real.log (231382216191 / 250000000000) ∧
    -Real.log (231382216191 / 250000000000) ≤ (1934749 / 25000000) := by
  have h := checkLog_sound (w := (18617783809 / 481382216191)) (n := 12)
    (lo := (77389959 / 1000000000)) (hi := (1934749 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 231382216191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 231382216191) = 1/(231382216191 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12630 : Bounds (-1934749 / 25000000) (-77389959 / 1000000000) (Real.log (231382216191 / 250000000000)) := by
  have h := reflection_log_12630_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12631_neg : (19018973 / 250000000) ≤ -Real.log (37069834839 / 40000000000) ∧
    -Real.log (37069834839 / 40000000000) ≤ (76075893 / 1000000000) := by
  have h := checkLog_sound (w := (2930165161 / 77069834839)) (n := 12)
    (lo := (19018973 / 250000000)) (hi := (76075893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 37069834839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 37069834839) = 1/(37069834839 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12631 : Bounds (-76075893 / 1000000000) (-19018973 / 250000000) (Real.log (37069834839 / 40000000000)) := by
  have h := reflection_log_12631_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12632_neg : (555140923 / 1000000000) ≤ -Real.log (100000000000 / 174218648239) ∧
    -Real.log (100000000000 / 174218648239) ≤ (138785231 / 250000000) := by
  have h := checkLog_sound (w := (74218648239 / 274218648239)) (n := 12)
    (lo := (555140923 / 1000000000)) (hi := (138785231 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((174218648239 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(174218648239 / 100000000000) = 1/(100000000000 / 174218648239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12632 : Bounds (555140923 / 1000000000) (138785231 / 250000000) (Real.log (174218648239 / 100000000000)) := by
  have h := reflection_log_12632_neg
  have he : Real.log (174218648239 / 100000000000) = -Real.log (100000000000 / 174218648239) := by
    rw [show ((174218648239 / 100000000000) : ℝ) = ((100000000000 / 174218648239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12633_neg : (111995211 / 200000000) ≤ -Real.log (500000000000 / 875315291031) ∧
    -Real.log (500000000000 / 875315291031) ≤ (69997007 / 125000000) := by
  have h := checkLog_sound (w := (375315291031 / 1375315291031)) (n := 12)
    (lo := (111995211 / 200000000)) (hi := (69997007 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((875315291031 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(875315291031 / 500000000000) = 1/(500000000000 / 875315291031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12633 : Bounds (111995211 / 200000000) (69997007 / 125000000) (Real.log (875315291031 / 500000000000)) := by
  have h := reflection_log_12633_neg
  have he : Real.log (875315291031 / 500000000000) = -Real.log (500000000000 / 875315291031) := by
    rw [show ((875315291031 / 500000000000) : ℝ) = ((500000000000 / 875315291031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12634_neg : (569510913 / 500000000) ≤ -Real.log (500000000000 / 1561855670103) ∧
    -Real.log (500000000000 / 1561855670103) ≤ (284755457 / 250000000) := by
  have h := checkLog_sound (w := (561855670103 / 2561855670103)) (n := 12)
    (lo := (222937323 / 500000000)) (hi := (445874647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1561855670103 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1561855670103 / 1000000000000) = 1/(500000000000 / 1561855670103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12634 : Bounds (569510913 / 500000000) (284755457 / 250000000) (Real.log (1561855670103 / 500000000000)) := by
  have h := reflection_log_12634_neg
  have he : Real.log (1561855670103 / 500000000000) = -Real.log (500000000000 / 1561855670103) := by
    rw [show ((1561855670103 / 500000000000) : ℝ) = ((500000000000 / 1561855670103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12635_neg : (1147204843 / 1000000000) ≤ -Real.log (500000000000 / 1574688796681) ∧
    -Real.log (500000000000 / 1574688796681) ≤ (229440969 / 200000000) := by
  have h := checkLog_sound (w := (574688796681 / 2574688796681)) (n := 12)
    (lo := (454057663 / 1000000000)) (hi := (7094651 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1574688796681 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1574688796681 / 1000000000000) = 1/(500000000000 / 1574688796681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12635 : Bounds (1147204843 / 1000000000) (229440969 / 200000000) (Real.log (1574688796681 / 500000000000)) := by
  have h := reflection_log_12635_neg
  have he : Real.log (1574688796681 / 500000000000) = -Real.log (500000000000 / 1574688796681) := by
    rw [show ((1574688796681 / 500000000000) : ℝ) = ((500000000000 / 1574688796681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12636_neg : (419368013 / 1000000000) ≤ -Real.log (1000 / 1521) ∧
    -Real.log (1000 / 1521) ≤ (209684007 / 500000000) := by
  have h := checkLog_sound (w := (521 / 2521)) (n := 12)
    (lo := (419368013 / 1000000000)) (hi := (209684007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1521 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1521 / 1000) = 1/(1000 / 1521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12636 : Bounds (419368013 / 1000000000) (209684007 / 500000000) (Real.log (1521 / 1000)) := by
  have h := reflection_log_12636_neg
  have he : Real.log (1521 / 1000) = -Real.log (1000 / 1521) := by
    rw [show ((1521 / 1000) : ℝ) = ((1000 / 1521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12637_neg : (736054681 / 1000000000) ≤ -Real.log (479 / 1000) ∧
    -Real.log (479 / 1000) ≤ (736054683 / 1000000000) := by
  have h := checkLog_sound (w := (21 / 979)) (n := 12)
    (lo := (42907501 / 1000000000)) (hi := (21453751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 479) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 479) = 1/(479 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12637 : Bounds (-736054683 / 1000000000) (-736054681 / 1000000000) (Real.log (479 / 1000)) := by
  have h := reflection_log_12637_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12638_neg : (16277 / 31250000) ≤ -Real.log (1000000 / 1000521) ∧
    -Real.log (1000000 / 1000521) ≤ (104173 / 200000000) := by
  have h := checkLog_sound (w := (521 / 2000521)) (n := 12)
    (lo := (16277 / 31250000)) (hi := (104173 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000521 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000521 / 1000000) = 1/(1000000 / 1000521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12638 : Bounds (16277 / 31250000) (104173 / 200000000) (Real.log (1000521 / 1000000)) := by
  have h := reflection_log_12638_neg
  have he : Real.log (1000521 / 1000000) = -Real.log (1000000 / 1000521) := by
    rw [show ((1000521 / 1000000) : ℝ) = ((1000000 / 1000521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12639_neg : (104227 / 200000000) ≤ -Real.log (999479 / 1000000) ∧
    -Real.log (999479 / 1000000) ≤ (32571 / 62500000) := by
  have h := checkLog_sound (w := (521 / 1999479)) (n := 12)
    (lo := (104227 / 200000000)) (hi := (32571 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999479) = 1/(999479 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12639 : Bounds (-32571 / 62500000) (-104227 / 200000000) (Real.log (999479 / 1000000)) := by
  have h := reflection_log_12639_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12640_neg : (30113503 / 125000000) ≤ -Real.log (250000 / 318101) ∧
    -Real.log (250000 / 318101) ≤ (9636321 / 40000000) := by
  have h := checkLog_sound (w := (68101 / 568101)) (n := 12)
    (lo := (30113503 / 125000000)) (hi := (9636321 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((318101 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(318101 / 250000) = 1/(250000 / 318101) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12640 : Bounds (30113503 / 125000000) (9636321 / 40000000) (Real.log (318101 / 250000)) := by
  have h := reflection_log_12640_neg
  have he : Real.log (318101 / 250000) = -Real.log (250000 / 318101) := by
    rw [show ((318101 / 250000) : ℝ) = ((250000 / 318101) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12641_neg : (318009329 / 1000000000) ≤ -Real.log (181899 / 250000) ∧
    -Real.log (181899 / 250000) ≤ (31800933 / 100000000) := by
  have h := checkLog_sound (w := (68101 / 431899)) (n := 12)
    (lo := (318009329 / 1000000000)) (hi := (31800933 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 181899) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 181899) = 1/(181899 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12641 : Bounds (-31800933 / 100000000) (-318009329 / 1000000000) (Real.log (181899 / 250000)) := by
  have h := reflection_log_12641_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12642_neg : (121335423 / 500000000) ≤ -Real.log (1000000 / 1274649) ∧
    -Real.log (1000000 / 1274649) ≤ (242670847 / 1000000000) := by
  have h := checkLog_sound (w := (274649 / 2274649)) (n := 12)
    (lo := (121335423 / 500000000)) (hi := (242670847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1274649 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1274649 / 1000000) = 1/(1000000 / 1274649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12642 : Bounds (121335423 / 500000000) (242670847 / 1000000000) (Real.log (1274649 / 1000000)) := by
  have h := reflection_log_12642_neg
  have he : Real.log (1274649 / 1000000) = -Real.log (1000000 / 1274649) := by
    rw [show ((1274649 / 1000000) : ℝ) = ((1000000 / 1274649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12643_neg : (321099603 / 1000000000) ≤ -Real.log (725351 / 1000000) ∧
    -Real.log (725351 / 1000000) ≤ (80274901 / 250000000) := by
  have h := checkLog_sound (w := (274649 / 1725351)) (n := 12)
    (lo := (321099603 / 1000000000)) (hi := (80274901 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 725351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 725351) = 1/(725351 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12643 : Bounds (-80274901 / 250000000) (-321099603 / 1000000000) (Real.log (725351 / 1000000)) := by
  have h := reflection_log_12643_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12644_neg : (19607189 / 250000000) ≤ -Real.log (924567926799 / 1000000000000) ∧
    -Real.log (924567926799 / 1000000000000) ≤ (78428757 / 1000000000) := by
  have h := checkLog_sound (w := (75432073201 / 1924567926799)) (n := 12)
    (lo := (19607189 / 250000000)) (hi := (78428757 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 924567926799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 924567926799) = 1/(924567926799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12644 : Bounds (-78428757 / 1000000000) (-19607189 / 250000000) (Real.log (924567926799 / 1000000000000)) := by
  have h := reflection_log_12644_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12645_neg : (15420261 / 200000000) ≤ -Real.log (57862253799 / 62500000000) ∧
    -Real.log (57862253799 / 62500000000) ≤ (38550653 / 500000000) := by
  have h := checkLog_sound (w := (4637746201 / 120362253799)) (n := 12)
    (lo := (15420261 / 200000000)) (hi := (38550653 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 57862253799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 57862253799) = 1/(57862253799 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12645 : Bounds (-38550653 / 500000000) (-15420261 / 200000000) (Real.log (57862253799 / 62500000000)) := by
  have h := reflection_log_12645_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12646_neg : (279458677 / 500000000) ≤ -Real.log (125000000000 / 218597271013) ∧
    -Real.log (125000000000 / 218597271013) ≤ (111783471 / 200000000) := by
  have h := checkLog_sound (w := (93597271013 / 343597271013)) (n := 12)
    (lo := (279458677 / 500000000)) (hi := (111783471 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218597271013 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218597271013 / 125000000000) = 1/(125000000000 / 218597271013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12646 : Bounds (279458677 / 500000000) (111783471 / 200000000) (Real.log (218597271013 / 125000000000)) := by
  have h := reflection_log_12646_neg
  have he : Real.log (218597271013 / 125000000000) = -Real.log (125000000000 / 218597271013) := by
    rw [show ((218597271013 / 125000000000) : ℝ) = ((125000000000 / 218597271013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12647_neg : (563770449 / 1000000000) ≤ -Real.log (500000000000 / 878642891511) ∧
    -Real.log (500000000000 / 878642891511) ≤ (11275409 / 20000000) := by
  have h := checkLog_sound (w := (378642891511 / 1378642891511)) (n := 12)
    (lo := (563770449 / 1000000000)) (hi := (11275409 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((878642891511 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(878642891511 / 500000000000) = 1/(500000000000 / 878642891511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12647 : Bounds (563770449 / 1000000000) (11275409 / 20000000) (Real.log (878642891511 / 500000000000)) := by
  have h := reflection_log_12647_neg
  have he : Real.log (878642891511 / 500000000000) = -Real.log (500000000000 / 878642891511) := by
    rw [show ((878642891511 / 500000000000) : ℝ) = ((500000000000 / 878642891511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12648_neg : (1147204843 / 1000000000) ≤ -Real.log (12500000000 / 39367219917) ∧
    -Real.log (12500000000 / 39367219917) ≤ (229440969 / 200000000) := by
  have h := checkLog_sound (w := (14367219917 / 64367219917)) (n := 12)
    (lo := (454057663 / 1000000000)) (hi := (7094651 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39367219917 / 25000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(39367219917 / 25000000000) = 1/(12500000000 / 39367219917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12648 : Bounds (1147204843 / 1000000000) (229440969 / 200000000) (Real.log (39367219917 / 12500000000)) := by
  have h := reflection_log_12648_neg
  have he : Real.log (39367219917 / 12500000000) = -Real.log (12500000000 / 39367219917) := by
    rw [show ((39367219917 / 12500000000) : ℝ) = ((12500000000 / 39367219917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12649_neg : (577711347 / 500000000) ≤ -Real.log (250000000000 / 793841336117) ∧
    -Real.log (250000000000 / 793841336117) ≤ (144427837 / 125000000) := by
  have h := checkLog_sound (w := (293841336117 / 1293841336117)) (n := 12)
    (lo := (231137757 / 500000000)) (hi := (92455103 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((793841336117 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(793841336117 / 500000000000) = 1/(250000000000 / 793841336117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12649 : Bounds (577711347 / 500000000) (144427837 / 125000000) (Real.log (793841336117 / 250000000000)) := by
  have h := reflection_log_12649_neg
  have he : Real.log (793841336117 / 250000000000) = -Real.log (250000000000 / 793841336117) := by
    rw [show ((793841336117 / 250000000000) : ℝ) = ((250000000000 / 793841336117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12650_neg : (421338457 / 1000000000) ≤ -Real.log (250 / 381) ∧
    -Real.log (250 / 381) ≤ (210669229 / 500000000) := by
  have h := checkLog_sound (w := (131 / 631)) (n := 12)
    (lo := (421338457 / 1000000000)) (hi := (210669229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((381 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(381 / 250) = 1/(250 / 381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12650 : Bounds (421338457 / 1000000000) (210669229 / 500000000) (Real.log (381 / 250)) := by
  have h := reflection_log_12650_neg
  have he : Real.log (381 / 250) = -Real.log (250 / 381) := by
    rw [show ((381 / 250) : ℝ) = ((250 / 381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12651_neg : (46396089 / 62500000) ≤ -Real.log (119 / 250) ∧
    -Real.log (119 / 250) ≤ (371168713 / 500000000) := by
  have h := checkLog_sound (w := (3 / 122)) (n := 12)
    (lo := (12297561 / 250000000)) (hi := (9838049 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 119) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 119) = 1/(119 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12651 : Bounds (-371168713 / 500000000) (-46396089 / 62500000) (Real.log (119 / 250)) := by
  have h := reflection_log_12651_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12652_neg : (261931 / 500000000) ≤ -Real.log (250000 / 250131) ∧
    -Real.log (250000 / 250131) ≤ (523863 / 1000000000) := by
  have h := checkLog_sound (w := (131 / 500131)) (n := 12)
    (lo := (261931 / 500000000)) (hi := (523863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250131 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250131 / 250000) = 1/(250000 / 250131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12652 : Bounds (261931 / 500000000) (523863 / 1000000000) (Real.log (250131 / 250000)) := by
  have h := reflection_log_12652_neg
  have he : Real.log (250131 / 250000) = -Real.log (250000 / 250131) := by
    rw [show ((250131 / 250000) : ℝ) = ((250000 / 250131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12653_neg : (524137 / 1000000000) ≤ -Real.log (249869 / 250000) ∧
    -Real.log (249869 / 250000) ≤ (262069 / 500000000) := by
  have h := checkLog_sound (w := (131 / 499869)) (n := 12)
    (lo := (524137 / 1000000000)) (hi := (262069 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249869) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249869) = 1/(249869 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12653 : Bounds (-262069 / 500000000) (-524137 / 1000000000) (Real.log (249869 / 250000)) := by
  have h := reflection_log_12653_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12654_neg : (242284783 / 1000000000) ≤ -Real.log (1000000 / 1274157) ∧
    -Real.log (1000000 / 1274157) ≤ (15142799 / 62500000) := by
  have h := checkLog_sound (w := (274157 / 2274157)) (n := 12)
    (lo := (242284783 / 1000000000)) (hi := (15142799 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1274157 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1274157 / 1000000) = 1/(1000000 / 1274157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12654 : Bounds (242284783 / 1000000000) (15142799 / 62500000) (Real.log (1274157 / 1000000)) := by
  have h := reflection_log_12654_neg
  have he : Real.log (1274157 / 1000000) = -Real.log (1000000 / 1274157) := by
    rw [show ((1274157 / 1000000) : ℝ) = ((1000000 / 1274157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12655_neg : (16021077 / 50000000) ≤ -Real.log (725843 / 1000000) ∧
    -Real.log (725843 / 1000000) ≤ (320421541 / 1000000000) := by
  have h := checkLog_sound (w := (274157 / 1725843)) (n := 12)
    (lo := (16021077 / 50000000)) (hi := (320421541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 725843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 725843) = 1/(725843 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12655 : Bounds (-320421541 / 1000000000) (-16021077 / 50000000) (Real.log (725843 / 1000000)) := by
  have h := reflection_log_12655_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12656_neg : (244049099 / 1000000000) ≤ -Real.log (1000000 / 1276407) ∧
    -Real.log (1000000 / 1276407) ≤ (2440491 / 10000000) := by
  have h := checkLog_sound (w := (276407 / 2276407)) (n := 12)
    (lo := (244049099 / 1000000000)) (hi := (2440491 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1276407 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1276407 / 1000000) = 1/(1000000 / 1276407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12656 : Bounds (244049099 / 1000000000) (2440491 / 10000000) (Real.log (1276407 / 1000000)) := by
  have h := reflection_log_12656_neg
  have he : Real.log (1276407 / 1000000) = -Real.log (1000000 / 1276407) := by
    rw [show ((1276407 / 1000000) : ℝ) = ((1000000 / 1276407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12657_neg : (323526199 / 1000000000) ≤ -Real.log (723593 / 1000000) ∧
    -Real.log (723593 / 1000000) ≤ (1617631 / 5000000) := by
  have h := checkLog_sound (w := (276407 / 1723593)) (n := 12)
    (lo := (323526199 / 1000000000)) (hi := (1617631 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 723593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 723593) = 1/(723593 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12657 : Bounds (-1617631 / 5000000) (-323526199 / 1000000000) (Real.log (723593 / 1000000)) := by
  have h := reflection_log_12657_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12658_neg : (79477099 / 1000000000) ≤ -Real.log (923599170351 / 1000000000000) ∧
    -Real.log (923599170351 / 1000000000000) ≤ (794771 / 10000000) := by
  have h := checkLog_sound (w := (76400829649 / 1923599170351)) (n := 12)
    (lo := (79477099 / 1000000000)) (hi := (794771 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 923599170351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 923599170351) = 1/(923599170351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12658 : Bounds (-794771 / 10000000) (-79477099 / 1000000000) (Real.log (923599170351 / 1000000000000)) := by
  have h := reflection_log_12658_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12659_neg : (78136757 / 1000000000) ≤ -Real.log (924837939351 / 1000000000000) ∧
    -Real.log (924837939351 / 1000000000000) ≤ (39068379 / 500000000) := by
  have h := checkLog_sound (w := (75162060649 / 1924837939351)) (n := 12)
    (lo := (78136757 / 1000000000)) (hi := (39068379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 924837939351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 924837939351) = 1/(924837939351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12659 : Bounds (-39068379 / 500000000) (-78136757 / 1000000000) (Real.log (924837939351 / 1000000000000)) := by
  have h := reflection_log_12659_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12660_neg : (140676581 / 250000000) ≤ -Real.log (100000000000 / 175541680501) ∧
    -Real.log (100000000000 / 175541680501) ≤ (22508253 / 40000000) := by
  have h := checkLog_sound (w := (75541680501 / 275541680501)) (n := 12)
    (lo := (140676581 / 250000000)) (hi := (22508253 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175541680501 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175541680501 / 100000000000) = 1/(100000000000 / 175541680501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12660 : Bounds (140676581 / 250000000) (22508253 / 40000000) (Real.log (175541680501 / 100000000000)) := by
  have h := reflection_log_12660_neg
  have he : Real.log (175541680501 / 100000000000) = -Real.log (100000000000 / 175541680501) := by
    rw [show ((175541680501 / 100000000000) : ℝ) = ((100000000000 / 175541680501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12661_neg : (283787649 / 500000000) ≤ -Real.log (500000000000 / 881992363111) ∧
    -Real.log (500000000000 / 881992363111) ≤ (567575299 / 1000000000) := by
  have h := checkLog_sound (w := (381992363111 / 1381992363111)) (n := 12)
    (lo := (283787649 / 500000000)) (hi := (567575299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((881992363111 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(881992363111 / 500000000000) = 1/(500000000000 / 881992363111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12661 : Bounds (283787649 / 500000000) (567575299 / 1000000000) (Real.log (881992363111 / 500000000000)) := by
  have h := reflection_log_12661_neg
  have he : Real.log (881992363111 / 500000000000) = -Real.log (500000000000 / 881992363111) := by
    rw [show ((881992363111 / 500000000000) : ℝ) = ((500000000000 / 881992363111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12662_neg : (577711347 / 500000000) ≤ -Real.log (500000000000 / 1587682672233) ∧
    -Real.log (500000000000 / 1587682672233) ≤ (144427837 / 125000000) := by
  have h := checkLog_sound (w := (587682672233 / 2587682672233)) (n := 12)
    (lo := (231137757 / 500000000)) (hi := (92455103 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1587682672233 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1587682672233 / 1000000000000) = 1/(500000000000 / 1587682672233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12662 : Bounds (577711347 / 500000000) (144427837 / 125000000) (Real.log (1587682672233 / 500000000000)) := by
  have h := reflection_log_12662_neg
  have he : Real.log (1587682672233 / 500000000000) = -Real.log (500000000000 / 1587682672233) := by
    rw [show ((1587682672233 / 500000000000) : ℝ) = ((500000000000 / 1587682672233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12663_neg : (1163675881 / 1000000000) ≤ -Real.log (100000000000 / 320168067227) ∧
    -Real.log (100000000000 / 320168067227) ≤ (1163675883 / 1000000000) := by
  have h := checkLog_sound (w := (120168067227 / 520168067227)) (n := 12)
    (lo := (470528701 / 1000000000)) (hi := (235264351 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320168067227 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(320168067227 / 200000000000) = 1/(100000000000 / 320168067227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12663 : Bounds (1163675881 / 1000000000) (1163675883 / 1000000000) (Real.log (320168067227 / 100000000000)) := by
  have h := reflection_log_12663_neg
  have he : Real.log (320168067227 / 100000000000) = -Real.log (100000000000 / 320168067227) := by
    rw [show ((320168067227 / 100000000000) : ℝ) = ((100000000000 / 320168067227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12664_neg : (211652513 / 500000000) ≤ -Real.log (1000 / 1527) ∧
    -Real.log (1000 / 1527) ≤ (423305027 / 1000000000) := by
  have h := checkLog_sound (w := (527 / 2527)) (n := 12)
    (lo := (211652513 / 500000000)) (hi := (423305027 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1527 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1527 / 1000) = 1/(1000 / 1527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12664 : Bounds (211652513 / 500000000) (423305027 / 1000000000) (Real.log (1527 / 1000)) := by
  have h := reflection_log_12664_neg
  have he : Real.log (1527 / 1000) = -Real.log (1000 / 1527) := by
    rw [show ((1527 / 1000) : ℝ) = ((1000 / 1527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12665_neg : (748659889 / 1000000000) ≤ -Real.log (473 / 1000) ∧
    -Real.log (473 / 1000) ≤ (748659891 / 1000000000) := by
  have h := checkLog_sound (w := (27 / 973)) (n := 12)
    (lo := (55512709 / 1000000000)) (hi := (5551271 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 473) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 473) = 1/(473 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12665 : Bounds (-748659891 / 1000000000) (-748659889 / 1000000000) (Real.log (473 / 1000)) := by
  have h := reflection_log_12665_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12666_neg : (526861 / 1000000000) ≤ -Real.log (1000000 / 1000527) ∧
    -Real.log (1000000 / 1000527) ≤ (263431 / 500000000) := by
  have h := checkLog_sound (w := (527 / 2000527)) (n := 12)
    (lo := (526861 / 1000000000)) (hi := (263431 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000527 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000527 / 1000000) = 1/(1000000 / 1000527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12666 : Bounds (526861 / 1000000000) (263431 / 500000000) (Real.log (1000527 / 1000000)) := by
  have h := reflection_log_12666_neg
  have he : Real.log (1000527 / 1000000) = -Real.log (1000000 / 1000527) := by
    rw [show ((1000527 / 1000000) : ℝ) = ((1000000 / 1000527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12667_neg : (263569 / 500000000) ≤ -Real.log (999473 / 1000000) ∧
    -Real.log (999473 / 1000000) ≤ (527139 / 1000000000) := by
  have h := checkLog_sound (w := (527 / 1999473)) (n := 12)
    (lo := (263569 / 500000000)) (hi := (527139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999473) = 1/(999473 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12667 : Bounds (-527139 / 1000000000) (-263569 / 500000000) (Real.log (999473 / 1000000)) := by
  have h := reflection_log_12667_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12668_neg : (121831 / 500000) ≤ -Real.log (1000000 / 1275913) ∧
    -Real.log (1000000 / 1275913) ≤ (243662001 / 1000000000) := by
  have h := checkLog_sound (w := (275913 / 2275913)) (n := 12)
    (lo := (121831 / 500000)) (hi := (243662001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1275913 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1275913 / 1000000) = 1/(1000000 / 1275913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12668 : Bounds (121831 / 500000) (243662001 / 1000000000) (Real.log (1275913 / 1000000)) := by
  have h := reflection_log_12668_neg
  have he : Real.log (1275913 / 1000000) = -Real.log (1000000 / 1275913) := by
    rw [show ((1275913 / 1000000) : ℝ) = ((1000000 / 1275913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12669_neg : (20177733 / 62500000) ≤ -Real.log (724087 / 1000000) ∧
    -Real.log (724087 / 1000000) ≤ (322843729 / 1000000000) := by
  have h := checkLog_sound (w := (275913 / 1724087)) (n := 12)
    (lo := (20177733 / 62500000)) (hi := (322843729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 724087) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 724087) = 1/(724087 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12669 : Bounds (-322843729 / 1000000000) (-20177733 / 62500000) (Real.log (724087 / 1000000)) := by
  have h := reflection_log_12669_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_12670_neg : (49085717 / 200000000) ≤ -Real.log (1000000 / 1278169) ∧
    -Real.log (1000000 / 1278169) ≤ (122714293 / 500000000) := by
  have h := checkLog_sound (w := (278169 / 2278169)) (n := 12)
    (lo := (49085717 / 200000000)) (hi := (122714293 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1278169 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1278169 / 1000000) = 1/(1000000 / 1278169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12670 : Bounds (49085717 / 200000000) (122714293 / 500000000) (Real.log (1278169 / 1000000)) := by
  have h := reflection_log_12670_neg
  have he : Real.log (1278169 / 1000000) = -Real.log (1000000 / 1278169) := by
    rw [show ((1278169 / 1000000) : ℝ) = ((1000000 / 1278169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12671_neg : (325964239 / 1000000000) ≤ -Real.log (721831 / 1000000) ∧
    -Real.log (721831 / 1000000) ≤ (4074553 / 12500000) := by
  have h := checkLog_sound (w := (278169 / 1721831)) (n := 12)
    (lo := (325964239 / 1000000000)) (hi := (4074553 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 721831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 721831) = 1/(721831 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12671 : Bounds (-4074553 / 12500000) (-325964239 / 1000000000) (Real.log (721831 / 1000000)) := by
  have h := reflection_log_12671_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
