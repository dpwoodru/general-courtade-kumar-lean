import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13184_neg : (159449 / 250000000) ≤ -Real.log (500000 / 500319) ∧
    -Real.log (500000 / 500319) ≤ (637797 / 1000000000) := by
  have h := checkLog_sound (w := (319 / 1000319)) (n := 12)
    (lo := (159449 / 250000000)) (hi := (637797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500319 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500319 / 500000) = 1/(500000 / 500319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13184 : Bounds (159449 / 250000000) (637797 / 1000000000) (Real.log (500319 / 500000)) := by
  have h := reflection_log_13184_neg
  have he : Real.log (500319 / 500000) = -Real.log (500000 / 500319) := by
    rw [show ((500319 / 500000) : ℝ) = ((500000 / 500319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13185_neg : (638203 / 1000000000) ≤ -Real.log (499681 / 500000) ∧
    -Real.log (499681 / 500000) ≤ (159551 / 250000000) := by
  have h := checkLog_sound (w := (319 / 999681)) (n := 12)
    (lo := (638203 / 1000000000)) (hi := (159551 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499681) = 1/(499681 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13185 : Bounds (-159551 / 250000000) (-638203 / 1000000000) (Real.log (499681 / 500000)) := by
  have h := reflection_log_13185_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13186_neg : (295382349 / 1000000000) ≤ -Real.log (25000 / 33591) ∧
    -Real.log (25000 / 33591) ≤ (5907647 / 20000000) := by
  have h := checkLog_sound (w := (8591 / 58591)) (n := 12)
    (lo := (295382349 / 1000000000)) (hi := (5907647 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33591 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33591 / 25000) = 1/(25000 / 33591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13186 : Bounds (295382349 / 1000000000) (5907647 / 20000000) (Real.log (33591 / 25000)) := by
  have h := reflection_log_13186_neg
  have he : Real.log (33591 / 25000) = -Real.log (25000 / 33591) := by
    rw [show ((33591 / 25000) : ℝ) = ((25000 / 33591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13187_neg : (21052293 / 50000000) ≤ -Real.log (16409 / 25000) ∧
    -Real.log (16409 / 25000) ≤ (421045861 / 1000000000) := by
  have h := checkLog_sound (w := (8591 / 41409)) (n := 12)
    (lo := (21052293 / 50000000)) (hi := (421045861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 16409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 16409) = 1/(16409 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13187 : Bounds (-421045861 / 1000000000) (-21052293 / 50000000) (Real.log (16409 / 25000)) := by
  have h := reflection_log_13187_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13188_neg : (14861839 / 50000000) ≤ -Real.log (500000 / 673067) ∧
    -Real.log (500000 / 673067) ≤ (297236781 / 1000000000) := by
  have h := checkLog_sound (w := (173067 / 1173067)) (n := 12)
    (lo := (14861839 / 50000000)) (hi := (297236781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((673067 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(673067 / 500000) = 1/(500000 / 673067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13188 : Bounds (14861839 / 50000000) (297236781 / 1000000000) (Real.log (673067 / 500000)) := by
  have h := reflection_log_13188_neg
  have he : Real.log (673067 / 500000) = -Real.log (500000 / 673067) := by
    rw [show ((673067 / 500000) : ℝ) = ((500000 / 673067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13189_neg : (424852841 / 1000000000) ≤ -Real.log (326933 / 500000) ∧
    -Real.log (326933 / 500000) ≤ (212426421 / 500000000) := by
  have h := checkLog_sound (w := (173067 / 826933)) (n := 12)
    (lo := (424852841 / 1000000000)) (hi := (212426421 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 326933) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 326933) = 1/(326933 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13189 : Bounds (-212426421 / 500000000) (-424852841 / 1000000000) (Real.log (326933 / 500000)) := by
  have h := reflection_log_13189_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13190_neg : (6380803 / 50000000) ≤ -Real.log (220047813511 / 250000000000) ∧
    -Real.log (220047813511 / 250000000000) ≤ (127616061 / 1000000000) := by
  have h := checkLog_sound (w := (29952186489 / 470047813511)) (n := 12)
    (lo := (6380803 / 50000000)) (hi := (127616061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 220047813511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 220047813511) = 1/(220047813511 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13190 : Bounds (-127616061 / 1000000000) (-6380803 / 50000000) (Real.log (220047813511 / 250000000000)) := by
  have h := reflection_log_13190_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13191_neg : (12566351 / 100000000) ≤ -Real.log (551194719 / 625000000) ∧
    -Real.log (551194719 / 625000000) ≤ (125663511 / 1000000000) := by
  have h := checkLog_sound (w := (73805281 / 1176194719)) (n := 12)
    (lo := (12566351 / 100000000)) (hi := (125663511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000000 / 551194719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000000 / 551194719) = 1/(551194719 / 625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13191 : Bounds (-125663511 / 1000000000) (-12566351 / 100000000) (Real.log (551194719 / 625000000)) := by
  have h := reflection_log_13191_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13192_neg : (44776763 / 62500000) ≤ -Real.log (250000000000 / 511777073557) ∧
    -Real.log (250000000000 / 511777073557) ≤ (71642821 / 100000000) := by
  have h := checkLog_sound (w := (11777073557 / 1011777073557)) (n := 12)
    (lo := (5820257 / 250000000)) (hi := (23281029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((511777073557 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(511777073557 / 500000000000) = 1/(250000000000 / 511777073557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13192 : Bounds (44776763 / 62500000) (71642821 / 100000000) (Real.log (511777073557 / 250000000000)) := by
  have h := reflection_log_13192_neg
  have he : Real.log (511777073557 / 250000000000) = -Real.log (250000000000 / 511777073557) := by
    rw [show ((511777073557 / 250000000000) : ℝ) = ((250000000000 / 511777073557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13193_neg : (722089621 / 1000000000) ≤ -Real.log (50000000000 / 102936534397) ∧
    -Real.log (50000000000 / 102936534397) ≤ (722089623 / 1000000000) := by
  have h := checkLog_sound (w := (2936534397 / 202936534397)) (n := 12)
    (lo := (28942441 / 1000000000)) (hi := (14471221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102936534397 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(102936534397 / 100000000000) = 1/(50000000000 / 102936534397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13193 : Bounds (722089621 / 1000000000) (722089623 / 1000000000) (Real.log (102936534397 / 50000000000)) := by
  have h := reflection_log_13193_neg
  have he : Real.log (102936534397 / 50000000000) = -Real.log (50000000000 / 102936534397) := by
    rw [show ((102936534397 / 50000000000) : ℝ) = ((50000000000 / 102936534397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13194_neg : (187437591 / 125000000) ≤ -Real.log (500000000000 / 2239726027397) ∧
    -Real.log (500000000000 / 2239726027397) ≤ (1499500731 / 1000000000) := by
  have h := checkLog_sound (w := (239726027397 / 4239726027397)) (n := 12)
    (lo := (3537699 / 31250000)) (hi := (113206369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2239726027397 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2239726027397 / 2000000000000) = 1/(500000000000 / 2239726027397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13194 : Bounds (187437591 / 125000000) (1499500731 / 1000000000) (Real.log (2239726027397 / 500000000000)) := by
  have h := reflection_log_13194_neg
  have he : Real.log (2239726027397 / 500000000000) = -Real.log (500000000000 / 2239726027397) := by
    rw [show ((2239726027397 / 500000000000) : ℝ) = ((500000000000 / 2239726027397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13195_neg : (1509587051 / 1000000000) ≤ -Real.log (500000000000 / 2262430939227) ∧
    -Real.log (500000000000 / 2262430939227) ≤ (754793527 / 500000000) := by
  have h := checkLog_sound (w := (262430939227 / 4262430939227)) (n := 12)
    (lo := (123292691 / 1000000000)) (hi := (30823173 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2262430939227 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2262430939227 / 2000000000000) = 1/(500000000000 / 2262430939227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13195 : Bounds (1509587051 / 1000000000) (754793527 / 500000000) (Real.log (2262430939227 / 500000000000)) := by
  have h := reflection_log_13195_neg
  have he : Real.log (2262430939227 / 500000000000) = -Real.log (500000000000 / 2262430939227) := by
    rw [show ((2262430939227 / 500000000000) : ℝ) = ((500000000000 / 2262430939227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13196_neg : (123826453 / 250000000) ≤ -Real.log (1000 / 1641) ∧
    -Real.log (1000 / 1641) ≤ (495305813 / 1000000000) := by
  have h := checkLog_sound (w := (641 / 2641)) (n := 12)
    (lo := (123826453 / 250000000)) (hi := (495305813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1641 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1641 / 1000) = 1/(1000 / 1641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13196 : Bounds (123826453 / 250000000) (495305813 / 1000000000) (Real.log (1641 / 1000)) := by
  have h := reflection_log_13196_neg
  have he : Real.log (1641 / 1000) = -Real.log (1000 / 1641) := by
    rw [show ((1641 / 1000) : ℝ) = ((1000 / 1641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13197_neg : (1024432889 / 1000000000) ≤ -Real.log (359 / 1000) ∧
    -Real.log (359 / 1000) ≤ (1024432891 / 1000000000) := by
  have h := checkLog_sound (w := (141 / 859)) (n := 12)
    (lo := (331285709 / 1000000000)) (hi := (33128571 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 359) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 359) = 1/(359 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13197 : Bounds (-1024432891 / 1000000000) (-1024432889 / 1000000000) (Real.log (359 / 1000)) := by
  have h := reflection_log_13197_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13198_neg : (320397 / 500000000) ≤ -Real.log (1000000 / 1000641) ∧
    -Real.log (1000000 / 1000641) ≤ (128159 / 200000000) := by
  have h := checkLog_sound (w := (641 / 2000641)) (n := 12)
    (lo := (320397 / 500000000)) (hi := (128159 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000641 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000641 / 1000000) = 1/(1000000 / 1000641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13198 : Bounds (320397 / 500000000) (128159 / 200000000) (Real.log (1000641 / 1000000)) := by
  have h := reflection_log_13198_neg
  have he : Real.log (1000641 / 1000000) = -Real.log (1000000 / 1000641) := by
    rw [show ((1000641 / 1000000) : ℝ) = ((1000000 / 1000641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13199_neg : (128241 / 200000000) ≤ -Real.log (999359 / 1000000) ∧
    -Real.log (999359 / 1000000) ≤ (320603 / 500000000) := by
  have h := checkLog_sound (w := (641 / 1999359)) (n := 12)
    (lo := (128241 / 200000000)) (hi := (320603 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999359) = 1/(999359 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13199 : Bounds (-320603 / 500000000) (-128241 / 200000000) (Real.log (999359 / 1000000)) := by
  have h := reflection_log_13199_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13200_neg : (296806567 / 1000000000) ≤ -Real.log (200000 / 269111) ∧
    -Real.log (200000 / 269111) ≤ (37100821 / 125000000) := by
  have h := checkLog_sound (w := (69111 / 469111)) (n := 12)
    (lo := (296806567 / 1000000000)) (hi := (37100821 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269111 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269111 / 200000) = 1/(200000 / 269111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13200 : Bounds (296806567 / 1000000000) (37100821 / 125000000) (Real.log (269111 / 200000)) := by
  have h := reflection_log_13200_neg
  have he : Real.log (269111 / 200000) = -Real.log (200000 / 269111) := by
    rw [show ((269111 / 200000) : ℝ) = ((200000 / 269111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13201_neg : (42396773 / 100000000) ≤ -Real.log (130889 / 200000) ∧
    -Real.log (130889 / 200000) ≤ (423967731 / 1000000000) := by
  have h := checkLog_sound (w := (69111 / 330889)) (n := 12)
    (lo := (42396773 / 100000000)) (hi := (423967731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 130889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 130889) = 1/(130889 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13201 : Bounds (-423967731 / 1000000000) (-42396773 / 100000000) (Real.log (130889 / 200000)) := by
  have h := reflection_log_13201_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13202_neg : (37333037 / 125000000) ≤ -Real.log (1000000 / 1348057) ∧
    -Real.log (1000000 / 1348057) ≤ (298664297 / 1000000000) := by
  have h := checkLog_sound (w := (348057 / 2348057)) (n := 12)
    (lo := (37333037 / 125000000)) (hi := (298664297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1348057 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1348057 / 1000000) = 1/(1000000 / 1348057) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13202 : Bounds (37333037 / 125000000) (298664297 / 1000000000) (Real.log (1348057 / 1000000)) := by
  have h := reflection_log_13202_neg
  have he : Real.log (1348057 / 1000000) = -Real.log (1000000 / 1348057) := by
    rw [show ((1348057 / 1000000) : ℝ) = ((1000000 / 1348057) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13203_neg : (3342173 / 7812500) ≤ -Real.log (651943 / 1000000) ∧
    -Real.log (651943 / 1000000) ≤ (85559629 / 200000000) := by
  have h := checkLog_sound (w := (348057 / 1651943)) (n := 12)
    (lo := (3342173 / 7812500)) (hi := (85559629 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 651943) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 651943) = 1/(651943 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13203 : Bounds (-85559629 / 200000000) (-3342173 / 7812500) (Real.log (651943 / 1000000)) := by
  have h := reflection_log_13203_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13204_neg : (129133847 / 1000000000) ≤ -Real.log (878856324751 / 1000000000000) ∧
    -Real.log (878856324751 / 1000000000000) ≤ (16141731 / 125000000) := by
  have h := checkLog_sound (w := (121143675249 / 1878856324751)) (n := 12)
    (lo := (129133847 / 1000000000)) (hi := (16141731 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 878856324751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 878856324751) = 1/(878856324751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13204 : Bounds (-16141731 / 125000000) (-129133847 / 1000000000) (Real.log (878856324751 / 1000000000000)) := by
  have h := reflection_log_13204_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13205_neg : (127161163 / 1000000000) ≤ -Real.log (35223669679 / 40000000000) ∧
    -Real.log (35223669679 / 40000000000) ≤ (31790291 / 250000000) := by
  have h := checkLog_sound (w := (4776330321 / 75223669679)) (n := 12)
    (lo := (127161163 / 1000000000)) (hi := (31790291 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 35223669679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 35223669679) = 1/(35223669679 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13205 : Bounds (-31790291 / 250000000) (-127161163 / 1000000000) (Real.log (35223669679 / 40000000000)) := by
  have h := reflection_log_13205_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13206_neg : (720774297 / 1000000000) ≤ -Real.log (250000000000 / 514006142609) ∧
    -Real.log (250000000000 / 514006142609) ≤ (720774299 / 1000000000) := by
  have h := checkLog_sound (w := (14006142609 / 1014006142609)) (n := 12)
    (lo := (27627117 / 1000000000)) (hi := (13813559 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((514006142609 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(514006142609 / 500000000000) = 1/(250000000000 / 514006142609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13206 : Bounds (720774297 / 1000000000) (720774299 / 1000000000) (Real.log (514006142609 / 250000000000)) := by
  have h := reflection_log_13206_neg
  have he : Real.log (514006142609 / 250000000000) = -Real.log (250000000000 / 514006142609) := by
    rw [show ((514006142609 / 250000000000) : ℝ) = ((250000000000 / 514006142609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13207_neg : (18161561 / 25000000) ≤ -Real.log (62500000000 / 129234553481) ∧
    -Real.log (62500000000 / 129234553481) ≤ (363231221 / 500000000) := by
  have h := checkLog_sound (w := (4234553481 / 254234553481)) (n := 12)
    (lo := (1665763 / 50000000)) (hi := (33315261 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((129234553481 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(129234553481 / 125000000000) = 1/(62500000000 / 129234553481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13207 : Bounds (18161561 / 25000000) (363231221 / 500000000) (Real.log (129234553481 / 62500000000)) := by
  have h := reflection_log_13207_neg
  have he : Real.log (129234553481 / 62500000000) = -Real.log (62500000000 / 129234553481) := by
    rw [show ((129234553481 / 62500000000) : ℝ) = ((62500000000 / 129234553481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13208_neg : (1509587051 / 1000000000) ≤ -Real.log (250000000000 / 1131215469613) ∧
    -Real.log (250000000000 / 1131215469613) ≤ (754793527 / 500000000) := by
  have h := checkLog_sound (w := (131215469613 / 2131215469613)) (n := 12)
    (lo := (123292691 / 1000000000)) (hi := (30823173 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1131215469613 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1131215469613 / 1000000000000) = 1/(250000000000 / 1131215469613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13208 : Bounds (1509587051 / 1000000000) (754793527 / 500000000) (Real.log (1131215469613 / 250000000000)) := by
  have h := reflection_log_13208_neg
  have he : Real.log (1131215469613 / 250000000000) = -Real.log (250000000000 / 1131215469613) := by
    rw [show ((1131215469613 / 250000000000) : ℝ) = ((250000000000 / 1131215469613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13209_neg : (1519738701 / 1000000000) ≤ -Real.log (100000000000 / 457103064067) ∧
    -Real.log (100000000000 / 457103064067) ≤ (94983669 / 62500000) := by
  have h := checkLog_sound (w := (57103064067 / 857103064067)) (n := 12)
    (lo := (133444341 / 1000000000)) (hi := (66722171 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((457103064067 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(457103064067 / 400000000000) = 1/(100000000000 / 457103064067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13209 : Bounds (1519738701 / 1000000000) (94983669 / 62500000) (Real.log (457103064067 / 100000000000)) := by
  have h := reflection_log_13209_neg
  have he : Real.log (457103064067 / 100000000000) = -Real.log (100000000000 / 457103064067) := by
    rw [show ((457103064067 / 100000000000) : ℝ) = ((100000000000 / 457103064067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13210_neg : (62141537 / 125000000) ≤ -Real.log (250 / 411) ∧
    -Real.log (250 / 411) ≤ (497132297 / 1000000000) := by
  have h := checkLog_sound (w := (161 / 661)) (n := 12)
    (lo := (62141537 / 125000000)) (hi := (497132297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((411 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(411 / 250) = 1/(250 / 411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13210 : Bounds (62141537 / 125000000) (497132297 / 1000000000) (Real.log (411 / 250)) := by
  have h := reflection_log_13210_neg
  have he : Real.log (411 / 250) = -Real.log (250 / 411) := by
    rw [show ((411 / 250) : ℝ) = ((250 / 411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13211_neg : (1032824547 / 1000000000) ≤ -Real.log (89 / 250) ∧
    -Real.log (89 / 250) ≤ (1032824549 / 1000000000) := by
  have h := checkLog_sound (w := (18 / 107)) (n := 12)
    (lo := (339677367 / 1000000000)) (hi := (42459671 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 89) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 89) = 1/(89 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13211 : Bounds (-1032824549 / 1000000000) (-1032824547 / 1000000000) (Real.log (89 / 250)) := by
  have h := reflection_log_13211_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13212_neg : (40237 / 62500000) ≤ -Real.log (250000 / 250161) ∧
    -Real.log (250000 / 250161) ≤ (643793 / 1000000000) := by
  have h := checkLog_sound (w := (161 / 500161)) (n := 12)
    (lo := (40237 / 62500000)) (hi := (643793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250161 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250161 / 250000) = 1/(250000 / 250161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13212 : Bounds (40237 / 62500000) (643793 / 1000000000) (Real.log (250161 / 250000)) := by
  have h := reflection_log_13212_neg
  have he : Real.log (250161 / 250000) = -Real.log (250000 / 250161) := by
    rw [show ((250161 / 250000) : ℝ) = ((250000 / 250161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13213_neg : (644207 / 1000000000) ≤ -Real.log (249839 / 250000) ∧
    -Real.log (249839 / 250000) ≤ (40263 / 62500000) := by
  have h := checkLog_sound (w := (161 / 499839)) (n := 12)
    (lo := (644207 / 1000000000)) (hi := (40263 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249839) = 1/(249839 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13213 : Bounds (-40263 / 62500000) (-644207 / 1000000000) (Real.log (249839 / 250000)) := by
  have h := reflection_log_13213_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13214_neg : (74558303 / 250000000) ≤ -Real.log (250000 / 336869) ∧
    -Real.log (250000 / 336869) ≤ (298233213 / 1000000000) := by
  have h := checkLog_sound (w := (86869 / 586869)) (n := 12)
    (lo := (74558303 / 250000000)) (hi := (298233213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((336869 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(336869 / 250000) = 1/(250000 / 336869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13214 : Bounds (74558303 / 250000000) (298233213 / 1000000000) (Real.log (336869 / 250000)) := by
  have h := reflection_log_13214_neg
  have he : Real.log (336869 / 250000) = -Real.log (250000 / 336869) := by
    rw [show ((336869 / 250000) : ℝ) = ((250000 / 336869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13215_neg : (213453679 / 500000000) ≤ -Real.log (163131 / 250000) ∧
    -Real.log (163131 / 250000) ≤ (426907359 / 1000000000) := by
  have h := checkLog_sound (w := (86869 / 413131)) (n := 12)
    (lo := (213453679 / 500000000)) (hi := (426907359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 163131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 163131) = 1/(163131 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13215 : Bounds (-426907359 / 1000000000) (-213453679 / 500000000) (Real.log (163131 / 250000)) := by
  have h := reflection_log_13215_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13216_neg : (15004637 / 50000000) ≤ -Real.log (31250 / 42187) ∧
    -Real.log (31250 / 42187) ≤ (300092741 / 1000000000) := by
  have h := checkLog_sound (w := (10937 / 73437)) (n := 12)
    (lo := (15004637 / 50000000)) (hi := (300092741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((42187 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(42187 / 31250) = 1/(31250 / 42187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13216 : Bounds (15004637 / 50000000) (300092741 / 1000000000) (Real.log (42187 / 31250)) := by
  have h := reflection_log_13216_neg
  have he : Real.log (42187 / 31250) = -Real.log (31250 / 42187) := by
    rw [show ((42187 / 31250) : ℝ) = ((31250 / 42187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13217_neg : (430758301 / 1000000000) ≤ -Real.log (20313 / 31250) ∧
    -Real.log (20313 / 31250) ≤ (215379151 / 500000000) := by
  have h := checkLog_sound (w := (10937 / 51563)) (n := 12)
    (lo := (430758301 / 1000000000)) (hi := (215379151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 20313) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 20313) = 1/(20313 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13217 : Bounds (-215379151 / 500000000) (-430758301 / 1000000000) (Real.log (20313 / 31250)) := by
  have h := reflection_log_13217_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13218_neg : (3266639 / 25000000) ≤ -Real.log (856944531 / 976562500) ∧
    -Real.log (856944531 / 976562500) ≤ (130665561 / 1000000000) := by
  have h := checkLog_sound (w := (119617969 / 1833507031)) (n := 12)
    (lo := (3266639 / 25000000)) (hi := (130665561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 856944531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 856944531) = 1/(856944531 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13218 : Bounds (-130665561 / 1000000000) (-3266639 / 25000000) (Real.log (856944531 / 976562500)) := by
  have h := reflection_log_13218_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13219_neg : (25734829 / 200000000) ≤ -Real.log (54953776839 / 62500000000) ∧
    -Real.log (54953776839 / 62500000000) ≤ (64337073 / 500000000) := by
  have h := checkLog_sound (w := (7546223161 / 117453776839)) (n := 12)
    (lo := (25734829 / 200000000)) (hi := (64337073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 54953776839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 54953776839) = 1/(54953776839 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13219 : Bounds (-64337073 / 500000000) (-25734829 / 200000000) (Real.log (54953776839 / 62500000000)) := by
  have h := reflection_log_13219_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13220_neg : (725140571 / 1000000000) ≤ -Real.log (500000000000 / 1032510681599) ∧
    -Real.log (500000000000 / 1032510681599) ≤ (725140573 / 1000000000) := by
  have h := checkLog_sound (w := (32510681599 / 2032510681599)) (n := 12)
    (lo := (31993391 / 1000000000)) (hi := (1999587 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1032510681599 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1032510681599 / 1000000000000) = 1/(500000000000 / 1032510681599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13220 : Bounds (725140571 / 1000000000) (725140573 / 1000000000) (Real.log (1032510681599 / 500000000000)) := by
  have h := reflection_log_13220_neg
  have he : Real.log (1032510681599 / 500000000000) = -Real.log (500000000000 / 1032510681599) := by
    rw [show ((1032510681599 / 500000000000) : ℝ) = ((500000000000 / 1032510681599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13221_neg : (4567819 / 6250000) ≤ -Real.log (125000000000 / 259605917393) ∧
    -Real.log (125000000000 / 259605917393) ≤ (365425521 / 500000000) := by
  have h := checkLog_sound (w := (9605917393 / 509605917393)) (n := 12)
    (lo := (1885193 / 50000000)) (hi := (37703861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259605917393 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(259605917393 / 250000000000) = 1/(125000000000 / 259605917393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13221 : Bounds (4567819 / 6250000) (365425521 / 500000000) (Real.log (259605917393 / 125000000000)) := by
  have h := reflection_log_13221_neg
  have he : Real.log (259605917393 / 125000000000) = -Real.log (125000000000 / 259605917393) := by
    rw [show ((259605917393 / 125000000000) : ℝ) = ((125000000000 / 259605917393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13222_neg : (1519738701 / 1000000000) ≤ -Real.log (250000000000 / 1142757660167) ∧
    -Real.log (250000000000 / 1142757660167) ≤ (94983669 / 62500000) := by
  have h := checkLog_sound (w := (142757660167 / 2142757660167)) (n := 12)
    (lo := (133444341 / 1000000000)) (hi := (66722171 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1142757660167 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1142757660167 / 1000000000000) = 1/(250000000000 / 1142757660167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13222 : Bounds (1519738701 / 1000000000) (94983669 / 62500000) (Real.log (1142757660167 / 250000000000)) := by
  have h := reflection_log_13222_neg
  have he : Real.log (1142757660167 / 250000000000) = -Real.log (250000000000 / 1142757660167) := by
    rw [show ((1142757660167 / 250000000000) : ℝ) = ((250000000000 / 1142757660167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13223_neg : (1529956843 / 1000000000) ≤ -Real.log (100000000000 / 461797752809) ∧
    -Real.log (100000000000 / 461797752809) ≤ (764978423 / 500000000) := by
  have h := checkLog_sound (w := (61797752809 / 861797752809)) (n := 12)
    (lo := (143662483 / 1000000000)) (hi := (35915621 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((461797752809 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(461797752809 / 400000000000) = 1/(100000000000 / 461797752809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13223 : Bounds (1529956843 / 1000000000) (764978423 / 500000000) (Real.log (461797752809 / 100000000000)) := by
  have h := reflection_log_13223_neg
  have he : Real.log (461797752809 / 100000000000) = -Real.log (100000000000 / 461797752809) := by
    rw [show ((461797752809 / 100000000000) : ℝ) = ((100000000000 / 461797752809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13224_neg : (498955451 / 1000000000) ≤ -Real.log (1000 / 1647) ∧
    -Real.log (1000 / 1647) ≤ (124738863 / 250000000) := by
  have h := checkLog_sound (w := (647 / 2647)) (n := 12)
    (lo := (498955451 / 1000000000)) (hi := (124738863 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1647 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1647 / 1000) = 1/(1000 / 1647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13224 : Bounds (498955451 / 1000000000) (124738863 / 250000000) (Real.log (1647 / 1000)) := by
  have h := reflection_log_13224_neg
  have he : Real.log (1647 / 1000) = -Real.log (1000 / 1647) := by
    rw [show ((1647 / 1000) : ℝ) = ((1000 / 1647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13225_neg : (1041287221 / 1000000000) ≤ -Real.log (353 / 1000) ∧
    -Real.log (353 / 1000) ≤ (1041287223 / 1000000000) := by
  have h := checkLog_sound (w := (147 / 853)) (n := 12)
    (lo := (348140041 / 1000000000)) (hi := (174070021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 353) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 353) = 1/(353 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13225 : Bounds (-1041287223 / 1000000000) (-1041287221 / 1000000000) (Real.log (353 / 1000)) := by
  have h := reflection_log_13225_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13226_neg : (64679 / 100000000) ≤ -Real.log (1000000 / 1000647) ∧
    -Real.log (1000000 / 1000647) ≤ (646791 / 1000000000) := by
  have h := checkLog_sound (w := (647 / 2000647)) (n := 12)
    (lo := (64679 / 100000000)) (hi := (646791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000647 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000647 / 1000000) = 1/(1000000 / 1000647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13226 : Bounds (64679 / 100000000) (646791 / 1000000000) (Real.log (1000647 / 1000000)) := by
  have h := reflection_log_13226_neg
  have he : Real.log (1000647 / 1000000) = -Real.log (1000000 / 1000647) := by
    rw [show ((1000647 / 1000000) : ℝ) = ((1000000 / 1000647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13227_neg : (647209 / 1000000000) ≤ -Real.log (999353 / 1000000) ∧
    -Real.log (999353 / 1000000) ≤ (64721 / 100000000) := by
  have h := checkLog_sound (w := (647 / 1999353)) (n := 12)
    (lo := (647209 / 1000000000)) (hi := (64721 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999353) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999353) = 1/(999353 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13227 : Bounds (-64721 / 100000000) (-647209 / 1000000000) (Real.log (999353 / 1000000)) := by
  have h := reflection_log_13227_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13228_neg : (299661531 / 1000000000) ≤ -Real.log (500000 / 674701) ∧
    -Real.log (500000 / 674701) ≤ (74915383 / 250000000) := by
  have h := checkLog_sound (w := (174701 / 1174701)) (n := 12)
    (lo := (299661531 / 1000000000)) (hi := (74915383 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((674701 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(674701 / 500000) = 1/(500000 / 674701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13228 : Bounds (299661531 / 1000000000) (74915383 / 250000000) (Real.log (674701 / 500000)) := by
  have h := reflection_log_13228_neg
  have he : Real.log (674701 / 500000) = -Real.log (500000 / 674701) := by
    rw [show ((674701 / 500000) : ℝ) = ((500000 / 674701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13229_neg : (429863339 / 1000000000) ≤ -Real.log (325299 / 500000) ∧
    -Real.log (325299 / 500000) ≤ (21493167 / 50000000) := by
  have h := checkLog_sound (w := (174701 / 825299)) (n := 12)
    (lo := (429863339 / 1000000000)) (hi := (21493167 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 325299) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 325299) = 1/(325299 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13229 : Bounds (-21493167 / 50000000) (-429863339 / 1000000000) (Real.log (325299 / 500000)) := by
  have h := reflection_log_13229_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13230_neg : (60304717 / 200000000) ≤ -Real.log (1000000 / 1351917) ∧
    -Real.log (1000000 / 1351917) ≤ (150761793 / 500000000) := by
  have h := checkLog_sound (w := (351917 / 2351917)) (n := 12)
    (lo := (60304717 / 200000000)) (hi := (150761793 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1351917 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1351917 / 1000000) = 1/(1000000 / 1351917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13230 : Bounds (60304717 / 200000000) (150761793 / 500000000) (Real.log (1351917 / 1000000)) := by
  have h := reflection_log_13230_neg
  have he : Real.log (1351917 / 1000000) = -Real.log (1000000 / 1351917) := by
    rw [show ((1351917 / 1000000) : ℝ) = ((1000000 / 1351917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13231_neg : (54217063 / 125000000) ≤ -Real.log (648083 / 1000000) ∧
    -Real.log (648083 / 1000000) ≤ (86747301 / 200000000) := by
  have h := checkLog_sound (w := (351917 / 1648083)) (n := 12)
    (lo := (54217063 / 125000000)) (hi := (86747301 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 648083) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 648083) = 1/(648083 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13231 : Bounds (-86747301 / 200000000) (-54217063 / 125000000) (Real.log (648083 / 1000000)) := by
  have h := reflection_log_13231_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13232_neg : (132212919 / 1000000000) ≤ -Real.log (876154425111 / 1000000000000) ∧
    -Real.log (876154425111 / 1000000000000) ≤ (3305323 / 25000000) := by
  have h := checkLog_sound (w := (123845574889 / 1876154425111)) (n := 12)
    (lo := (132212919 / 1000000000)) (hi := (3305323 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 876154425111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 876154425111) = 1/(876154425111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13232 : Bounds (-3305323 / 25000000) (-132212919 / 1000000000) (Real.log (876154425111 / 1000000000000)) := by
  have h := reflection_log_13232_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13233_neg : (130201807 / 1000000000) ≤ -Real.log (219479560599 / 250000000000) ∧
    -Real.log (219479560599 / 250000000000) ≤ (8137613 / 62500000) := by
  have h := checkLog_sound (w := (30520439401 / 469479560599)) (n := 12)
    (lo := (130201807 / 1000000000)) (hi := (8137613 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 219479560599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 219479560599) = 1/(219479560599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13233 : Bounds (-8137613 / 62500000) (-130201807 / 1000000000) (Real.log (219479560599 / 250000000000)) := by
  have h := reflection_log_13233_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13234_neg : (729524869 / 1000000000) ≤ -Real.log (500000000000 / 1037047454803) ∧
    -Real.log (500000000000 / 1037047454803) ≤ (729524871 / 1000000000) := by
  have h := checkLog_sound (w := (37047454803 / 2037047454803)) (n := 12)
    (lo := (36377689 / 1000000000)) (hi := (3637769 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1037047454803 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1037047454803 / 1000000000000) = 1/(500000000000 / 1037047454803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13234 : Bounds (729524869 / 1000000000) (729524871 / 1000000000) (Real.log (1037047454803 / 500000000000)) := by
  have h := reflection_log_13234_neg
  have he : Real.log (1037047454803 / 500000000000) = -Real.log (500000000000 / 1037047454803) := by
    rw [show ((1037047454803 / 500000000000) : ℝ) = ((500000000000 / 1037047454803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13235_neg : (735260089 / 1000000000) ≤ -Real.log (500000000000 / 1043012237631) ∧
    -Real.log (500000000000 / 1043012237631) ≤ (735260091 / 1000000000) := by
  have h := checkLog_sound (w := (43012237631 / 2043012237631)) (n := 12)
    (lo := (42112909 / 1000000000)) (hi := (4211291 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1043012237631 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1043012237631 / 1000000000000) = 1/(500000000000 / 1043012237631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13235 : Bounds (735260089 / 1000000000) (735260091 / 1000000000) (Real.log (1043012237631 / 500000000000)) := by
  have h := reflection_log_13235_neg
  have he : Real.log (1043012237631 / 500000000000) = -Real.log (500000000000 / 1043012237631) := by
    rw [show ((1043012237631 / 500000000000) : ℝ) = ((500000000000 / 1043012237631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13236_neg : (1529956843 / 1000000000) ≤ -Real.log (125000000000 / 577247191011) ∧
    -Real.log (125000000000 / 577247191011) ≤ (764978423 / 500000000) := by
  have h := checkLog_sound (w := (77247191011 / 1077247191011)) (n := 12)
    (lo := (143662483 / 1000000000)) (hi := (35915621 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((577247191011 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(577247191011 / 500000000000) = 1/(125000000000 / 577247191011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13236 : Bounds (1529956843 / 1000000000) (764978423 / 500000000) (Real.log (577247191011 / 125000000000)) := by
  have h := reflection_log_13236_neg
  have he : Real.log (577247191011 / 125000000000) = -Real.log (125000000000 / 577247191011) := by
    rw [show ((577247191011 / 125000000000) : ℝ) = ((125000000000 / 577247191011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13237_neg : (96265167 / 62500000) ≤ -Real.log (250000000000 / 1166430594901) ∧
    -Real.log (250000000000 / 1166430594901) ≤ (61609707 / 40000000) := by
  have h := checkLog_sound (w := (166430594901 / 2166430594901)) (n := 12)
    (lo := (19243539 / 125000000)) (hi := (153948313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1166430594901 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1166430594901 / 1000000000000) = 1/(250000000000 / 1166430594901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13237 : Bounds (96265167 / 62500000) (61609707 / 40000000) (Real.log (1166430594901 / 250000000000)) := by
  have h := reflection_log_13237_neg
  have he : Real.log (1166430594901 / 250000000000) = -Real.log (250000000000 / 1166430594901) := by
    rw [show ((1166430594901 / 250000000000) : ℝ) = ((250000000000 / 1166430594901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13238_neg : (500775287 / 1000000000) ≤ -Real.log (20 / 33) ∧
    -Real.log (20 / 33) ≤ (62596911 / 125000000) := by
  have h := checkLog_sound (w := (13 / 53)) (n := 12)
    (lo := (500775287 / 1000000000)) (hi := (62596911 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33 / 20) = 1/(20 / 33) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13238 : Bounds (500775287 / 1000000000) (62596911 / 125000000) (Real.log (33 / 20)) := by
  have h := reflection_log_13238_neg
  have he : Real.log (33 / 20) = -Real.log (20 / 33) := by
    rw [show ((33 / 20) : ℝ) = ((20 / 33) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13239_neg : (1049822123 / 1000000000) ≤ -Real.log (7 / 20) ∧
    -Real.log (7 / 20) ≤ (8398577 / 8000000) := by
  have h := checkLog_sound (w := (3 / 17)) (n := 12)
    (lo := (356674943 / 1000000000)) (hi := (2786523 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 7) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(10 / 7) = 1/(7 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13239 : Bounds (-8398577 / 8000000) (-1049822123 / 1000000000) (Real.log (7 / 20)) := by
  have h := reflection_log_13239_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13240_neg : (162447 / 250000000) ≤ -Real.log (20000 / 20013) ∧
    -Real.log (20000 / 20013) ≤ (649789 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 40013)) (n := 12)
    (lo := (162447 / 250000000)) (hi := (649789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20013 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20013 / 20000) = 1/(20000 / 20013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13240 : Bounds (162447 / 250000000) (649789 / 1000000000) (Real.log (20013 / 20000)) := by
  have h := reflection_log_13240_neg
  have he : Real.log (20013 / 20000) = -Real.log (20000 / 20013) := by
    rw [show ((20013 / 20000) : ℝ) = ((20000 / 20013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13241_neg : (650211 / 1000000000) ≤ -Real.log (19987 / 20000) ∧
    -Real.log (19987 / 20000) ≤ (162553 / 250000000) := by
  have h := checkLog_sound (w := (13 / 39987)) (n := 12)
    (lo := (650211 / 1000000000)) (hi := (162553 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 19987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 19987) = 1/(19987 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13241 : Bounds (-162553 / 250000000) (-650211 / 1000000000) (Real.log (19987 / 20000)) := by
  have h := reflection_log_13241_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13242_neg : (37636439 / 125000000) ≤ -Real.log (1000000 / 1351333) ∧
    -Real.log (1000000 / 1351333) ≤ (301091513 / 1000000000) := by
  have h := checkLog_sound (w := (351333 / 2351333)) (n := 12)
    (lo := (37636439 / 125000000)) (hi := (301091513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1351333 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1351333 / 1000000) = 1/(1000000 / 1351333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13242 : Bounds (37636439 / 125000000) (301091513 / 1000000000) (Real.log (1351333 / 1000000)) := by
  have h := reflection_log_13242_neg
  have he : Real.log (1351333 / 1000000) = -Real.log (1000000 / 1351333) := by
    rw [show ((1351333 / 1000000) : ℝ) = ((1000000 / 1351333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13243_neg : (432835791 / 1000000000) ≤ -Real.log (648667 / 1000000) ∧
    -Real.log (648667 / 1000000) ≤ (27052237 / 62500000) := by
  have h := checkLog_sound (w := (351333 / 1648667)) (n := 12)
    (lo := (432835791 / 1000000000)) (hi := (27052237 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 648667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 648667) = 1/(648667 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13243 : Bounds (-27052237 / 62500000) (-432835791 / 1000000000) (Real.log (648667 / 1000000)) := by
  have h := reflection_log_13243_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13244_neg : (151478039 / 500000000) ≤ -Real.log (200000 / 270771) ∧
    -Real.log (200000 / 270771) ≤ (302956079 / 1000000000) := by
  have h := checkLog_sound (w := (70771 / 470771)) (n := 12)
    (lo := (151478039 / 500000000)) (hi := (302956079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270771 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270771 / 200000) = 1/(200000 / 270771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13244 : Bounds (151478039 / 500000000) (302956079 / 1000000000) (Real.log (270771 / 200000)) := by
  have h := reflection_log_13244_neg
  have he : Real.log (270771 / 200000) = -Real.log (200000 / 270771) := by
    rw [show ((270771 / 200000) : ℝ) = ((200000 / 270771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13245_neg : (218365671 / 500000000) ≤ -Real.log (129229 / 200000) ∧
    -Real.log (129229 / 200000) ≤ (436731343 / 1000000000) := by
  have h := checkLog_sound (w := (70771 / 329229)) (n := 12)
    (lo := (218365671 / 500000000)) (hi := (436731343 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 129229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 129229) = 1/(129229 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13245 : Bounds (-436731343 / 1000000000) (-218365671 / 500000000) (Real.log (129229 / 200000)) := by
  have h := reflection_log_13245_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13246_neg : (133775263 / 1000000000) ≤ -Real.log (34991465559 / 40000000000) ∧
    -Real.log (34991465559 / 40000000000) ≤ (4180477 / 31250000) := by
  have h := checkLog_sound (w := (5008534441 / 74991465559)) (n := 12)
    (lo := (133775263 / 1000000000)) (hi := (4180477 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 34991465559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 34991465559) = 1/(34991465559 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13246 : Bounds (-4180477 / 31250000) (-133775263 / 1000000000) (Real.log (34991465559 / 40000000000)) := by
  have h := reflection_log_13246_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13247_neg : (65872139 / 500000000) ≤ -Real.log (876565123111 / 1000000000000) ∧
    -Real.log (876565123111 / 1000000000000) ≤ (131744279 / 1000000000) := by
  have h := checkLog_sound (w := (123434876889 / 1876565123111)) (n := 12)
    (lo := (65872139 / 500000000)) (hi := (131744279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 876565123111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 876565123111) = 1/(876565123111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13247 : Bounds (-131744279 / 1000000000) (-65872139 / 500000000) (Real.log (876565123111 / 1000000000000)) := by
  have h := reflection_log_13247_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
