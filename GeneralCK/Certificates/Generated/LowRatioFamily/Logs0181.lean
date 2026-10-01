import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11584_neg : (50718931 / 1000000000) ≤ -Real.log (950545801311 / 1000000000000) ∧
    -Real.log (950545801311 / 1000000000000) ≤ (12679733 / 250000000) := by
  have h := checkLog_sound (w := (49454198689 / 1950545801311)) (n := 12)
    (lo := (50718931 / 1000000000)) (hi := (12679733 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 950545801311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 950545801311) = 1/(950545801311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11584 : Bounds (-12679733 / 250000000) (-50718931 / 1000000000) (Real.log (950545801311 / 1000000000000)) := by
  have h := reflection_log_11584_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11585_neg : (113080849 / 250000000) ≤ -Real.log (20000000000 / 31439204647) ∧
    -Real.log (20000000000 / 31439204647) ≤ (452323397 / 1000000000) := by
  have h := checkLog_sound (w := (11439204647 / 51439204647)) (n := 12)
    (lo := (113080849 / 250000000)) (hi := (452323397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31439204647 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31439204647 / 20000000000) = 1/(20000000000 / 31439204647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11585 : Bounds (113080849 / 250000000) (452323397 / 1000000000) (Real.log (31439204647 / 20000000000)) := by
  have h := reflection_log_11585_neg
  have he : Real.log (31439204647 / 20000000000) = -Real.log (20000000000 / 31439204647) := by
    rw [show ((31439204647 / 20000000000) : ℝ) = ((20000000000 / 31439204647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11586_neg : (454366897 / 1000000000) ≤ -Real.log (100000000000 / 157517582013) ∧
    -Real.log (100000000000 / 157517582013) ≤ (227183449 / 500000000) := by
  have h := checkLog_sound (w := (57517582013 / 257517582013)) (n := 12)
    (lo := (454366897 / 1000000000)) (hi := (227183449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157517582013 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157517582013 / 100000000000) = 1/(100000000000 / 157517582013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11586 : Bounds (454366897 / 1000000000) (227183449 / 500000000) (Real.log (157517582013 / 100000000000)) := by
  have h := reflection_log_11586_neg
  have he : Real.log (157517582013 / 100000000000) = -Real.log (100000000000 / 157517582013) := by
    rw [show ((157517582013 / 100000000000) : ℝ) = ((100000000000 / 157517582013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11587_neg : (919793361 / 1000000000) ≤ -Real.log (31250000000 / 78399122807) ∧
    -Real.log (31250000000 / 78399122807) ≤ (919793363 / 1000000000) := by
  have h := checkLog_sound (w := (15899122807 / 140899122807)) (n := 12)
    (lo := (226646181 / 1000000000)) (hi := (113323091 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78399122807 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(78399122807 / 62500000000) = 1/(31250000000 / 78399122807) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11587 : Bounds (919793361 / 1000000000) (919793363 / 1000000000) (Real.log (78399122807 / 31250000000)) := by
  have h := reflection_log_11587_neg
  have he : Real.log (78399122807 / 31250000000) = -Real.log (31250000000 / 78399122807) := by
    rw [show ((78399122807 / 31250000000) : ℝ) = ((31250000000 / 78399122807) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11588_neg : (115281043 / 125000000) ≤ -Real.log (500000000000 / 1257469244289) ∧
    -Real.log (500000000000 / 1257469244289) ≤ (461124173 / 500000000) := by
  have h := checkLog_sound (w := (257469244289 / 2257469244289)) (n := 12)
    (lo := (57275291 / 250000000)) (hi := (45820233 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1257469244289 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1257469244289 / 1000000000000) = 1/(500000000000 / 1257469244289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11588 : Bounds (115281043 / 125000000) (461124173 / 500000000) (Real.log (1257469244289 / 500000000000)) := by
  have h := reflection_log_11588_neg
  have he : Real.log (1257469244289 / 500000000000) = -Real.log (500000000000 / 1257469244289) := by
    rw [show ((1257469244289 / 500000000000) : ℝ) = ((500000000000 / 1257469244289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11589_neg : (89768017 / 250000000) ≤ -Real.log (125 / 179) ∧
    -Real.log (125 / 179) ≤ (359072069 / 1000000000) := by
  have h := checkLog_sound (w := (27 / 152)) (n := 12)
    (lo := (89768017 / 250000000)) (hi := (359072069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(179 / 125) = 1/(125 / 179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11589 : Bounds (89768017 / 250000000) (359072069 / 1000000000) (Real.log (179 / 125)) := by
  have h := reflection_log_11589_neg
  have he : Real.log (179 / 125) = -Real.log (125 / 179) := by
    rw [show ((179 / 125) : ℝ) = ((125 / 179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11590_neg : (28281693 / 50000000) ≤ -Real.log (71 / 125) ∧
    -Real.log (71 / 125) ≤ (565633861 / 1000000000) := by
  have h := checkLog_sound (w := (27 / 98)) (n := 12)
    (lo := (28281693 / 50000000)) (hi := (565633861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 71) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 71) = 1/(71 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11590 : Bounds (-565633861 / 1000000000) (-28281693 / 50000000) (Real.log (71 / 125)) := by
  have h := reflection_log_11590_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11591_neg : (215953 / 500000000) ≤ -Real.log (62500 / 62527) ∧
    -Real.log (62500 / 62527) ≤ (431907 / 1000000000) := by
  have h := checkLog_sound (w := (27 / 125027)) (n := 12)
    (lo := (215953 / 500000000)) (hi := (431907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62527 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62527 / 62500) = 1/(62500 / 62527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11591 : Bounds (215953 / 500000000) (431907 / 1000000000) (Real.log (62527 / 62500)) := by
  have h := reflection_log_11591_neg
  have he : Real.log (62527 / 62500) = -Real.log (62500 / 62527) := by
    rw [show ((62527 / 62500) : ℝ) = ((62500 / 62527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11592_neg : (432093 / 1000000000) ≤ -Real.log (62473 / 62500) ∧
    -Real.log (62473 / 62500) ≤ (216047 / 500000000) := by
  have h := checkLog_sound (w := (27 / 124973)) (n := 12)
    (lo := (432093 / 1000000000)) (hi := (216047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62473) = 1/(62473 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11592 : Bounds (-216047 / 500000000) (-432093 / 1000000000) (Real.log (62473 / 62500)) := by
  have h := reflection_log_11592_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11593_neg : (1257851 / 6250000) ≤ -Real.log (500000 / 611469) ∧
    -Real.log (500000 / 611469) ≤ (201256161 / 1000000000) := by
  have h := checkLog_sound (w := (111469 / 1111469)) (n := 12)
    (lo := (1257851 / 6250000)) (hi := (201256161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((611469 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(611469 / 500000) = 1/(500000 / 611469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11593 : Bounds (1257851 / 6250000) (201256161 / 1000000000) (Real.log (611469 / 500000)) := by
  have h := reflection_log_11593_neg
  have he : Real.log (611469 / 500000) = -Real.log (500000 / 611469) := by
    rw [show ((611469 / 500000) : ℝ) = ((500000 / 611469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11594_neg : (252235137 / 1000000000) ≤ -Real.log (388531 / 500000) ∧
    -Real.log (388531 / 500000) ≤ (126117569 / 500000000) := by
  have h := checkLog_sound (w := (111469 / 888531)) (n := 12)
    (lo := (252235137 / 1000000000)) (hi := (126117569 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 388531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 388531) = 1/(388531 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11594 : Bounds (-126117569 / 500000000) (-252235137 / 1000000000) (Real.log (388531 / 500000)) := by
  have h := reflection_log_11594_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11595_neg : (202050651 / 1000000000) ≤ -Real.log (100000 / 122391) ∧
    -Real.log (100000 / 122391) ≤ (50512663 / 250000000) := by
  have h := checkLog_sound (w := (22391 / 222391)) (n := 12)
    (lo := (202050651 / 1000000000)) (hi := (50512663 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122391 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122391 / 100000) = 1/(100000 / 122391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11595 : Bounds (202050651 / 1000000000) (50512663 / 250000000) (Real.log (122391 / 100000)) := by
  have h := reflection_log_11595_neg
  have he : Real.log (122391 / 100000) = -Real.log (100000 / 122391) := by
    rw [show ((122391 / 100000) : ℝ) = ((100000 / 122391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11596_neg : (126743393 / 500000000) ≤ -Real.log (77609 / 100000) ∧
    -Real.log (77609 / 100000) ≤ (253486787 / 1000000000) := by
  have h := checkLog_sound (w := (22391 / 177609)) (n := 12)
    (lo := (126743393 / 500000000)) (hi := (253486787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 77609) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 77609) = 1/(77609 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11596 : Bounds (-253486787 / 1000000000) (-126743393 / 500000000) (Real.log (77609 / 100000)) := by
  have h := reflection_log_11596_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11597_neg : (25718067 / 500000000) ≤ -Real.log (9498643119 / 10000000000) ∧
    -Real.log (9498643119 / 10000000000) ≤ (10287227 / 200000000) := by
  have h := checkLog_sound (w := (501356881 / 19498643119)) (n := 12)
    (lo := (25718067 / 500000000)) (hi := (10287227 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9498643119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9498643119) = 1/(9498643119 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11597 : Bounds (-10287227 / 200000000) (-25718067 / 500000000) (Real.log (9498643119 / 10000000000)) := by
  have h := reflection_log_11597_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11598_neg : (50978977 / 1000000000) ≤ -Real.log (237574662039 / 250000000000) ∧
    -Real.log (237574662039 / 250000000000) ≤ (25489489 / 500000000) := by
  have h := checkLog_sound (w := (12425337961 / 487574662039)) (n := 12)
    (lo := (50978977 / 1000000000)) (hi := (25489489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 237574662039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 237574662039) = 1/(237574662039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11598 : Bounds (-25489489 / 500000000) (-50978977 / 1000000000) (Real.log (237574662039 / 250000000000)) := by
  have h := reflection_log_11598_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11599_neg : (226745649 / 500000000) ≤ -Real.log (500000000000 / 786898600111) ∧
    -Real.log (500000000000 / 786898600111) ≤ (453491299 / 1000000000) := by
  have h := checkLog_sound (w := (286898600111 / 1286898600111)) (n := 12)
    (lo := (226745649 / 500000000)) (hi := (453491299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((786898600111 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(786898600111 / 500000000000) = 1/(500000000000 / 786898600111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11599 : Bounds (226745649 / 500000000) (453491299 / 1000000000) (Real.log (786898600111 / 500000000000)) := by
  have h := reflection_log_11599_neg
  have he : Real.log (786898600111 / 500000000000) = -Real.log (500000000000 / 786898600111) := by
    rw [show ((786898600111 / 500000000000) : ℝ) = ((500000000000 / 786898600111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11600_neg : (227768719 / 500000000) ≤ -Real.log (500000000000 / 788510353181) ∧
    -Real.log (500000000000 / 788510353181) ≤ (455537439 / 1000000000) := by
  have h := checkLog_sound (w := (288510353181 / 1288510353181)) (n := 12)
    (lo := (227768719 / 500000000)) (hi := (455537439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((788510353181 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(788510353181 / 500000000000) = 1/(500000000000 / 788510353181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11600 : Bounds (227768719 / 500000000) (455537439 / 1000000000) (Real.log (788510353181 / 500000000000)) := by
  have h := reflection_log_11600_neg
  have he : Real.log (788510353181 / 500000000000) = -Real.log (500000000000 / 788510353181) := by
    rw [show ((788510353181 / 500000000000) : ℝ) = ((500000000000 / 788510353181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11601_neg : (115281043 / 125000000) ≤ -Real.log (3906250000 / 9823978471) ∧
    -Real.log (3906250000 / 9823978471) ≤ (461124173 / 500000000) := by
  have h := checkLog_sound (w := (2011478471 / 17636478471)) (n := 12)
    (lo := (57275291 / 250000000)) (hi := (45820233 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9823978471 / 7812500000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(9823978471 / 7812500000) = 1/(3906250000 / 9823978471) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11601 : Bounds (115281043 / 125000000) (461124173 / 500000000) (Real.log (9823978471 / 3906250000)) := by
  have h := reflection_log_11601_neg
  have he : Real.log (9823978471 / 3906250000) = -Real.log (3906250000 / 9823978471) := by
    rw [show ((9823978471 / 3906250000) : ℝ) = ((3906250000 / 9823978471) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11602_neg : (115588241 / 125000000) ≤ -Real.log (250000000000 / 630281690141) ∧
    -Real.log (250000000000 / 630281690141) ≤ (92470593 / 100000000) := by
  have h := checkLog_sound (w := (130281690141 / 1130281690141)) (n := 12)
    (lo := (57889687 / 250000000)) (hi := (231558749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((630281690141 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(630281690141 / 500000000000) = 1/(250000000000 / 630281690141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11602 : Bounds (115588241 / 125000000) (92470593 / 100000000) (Real.log (630281690141 / 250000000000)) := by
  have h := reflection_log_11602_neg
  have he : Real.log (630281690141 / 250000000000) = -Real.log (250000000000 / 630281690141) := by
    rw [show ((630281690141 / 250000000000) : ℝ) = ((250000000000 / 630281690141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11603_neg : (89942537 / 250000000) ≤ -Real.log (1000 / 1433) ∧
    -Real.log (1000 / 1433) ≤ (359770149 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 2433)) (n := 12)
    (lo := (89942537 / 250000000)) (hi := (359770149 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1433 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1433 / 1000) = 1/(1000 / 1433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11603 : Bounds (89942537 / 250000000) (359770149 / 1000000000) (Real.log (1433 / 1000)) := by
  have h := reflection_log_11603_neg
  have he : Real.log (1433 / 1000) = -Real.log (1000 / 1433) := by
    rw [show ((1433 / 1000) : ℝ) = ((1000 / 1433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11604_neg : (22695839 / 40000000) ≤ -Real.log (567 / 1000) ∧
    -Real.log (567 / 1000) ≤ (70924497 / 125000000) := by
  have h := checkLog_sound (w := (433 / 1567)) (n := 12)
    (lo := (22695839 / 40000000)) (hi := (70924497 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 567) = 1/(567 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11604 : Bounds (-70924497 / 125000000) (-22695839 / 40000000) (Real.log (567 / 1000)) := by
  have h := reflection_log_11604_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11605_neg : (216453 / 500000000) ≤ -Real.log (1000000 / 1000433) ∧
    -Real.log (1000000 / 1000433) ≤ (432907 / 1000000000) := by
  have h := checkLog_sound (w := (433 / 2000433)) (n := 12)
    (lo := (216453 / 500000000)) (hi := (432907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000433 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000433 / 1000000) = 1/(1000000 / 1000433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11605 : Bounds (216453 / 500000000) (432907 / 1000000000) (Real.log (1000433 / 1000000)) := by
  have h := reflection_log_11605_neg
  have he : Real.log (1000433 / 1000000) = -Real.log (1000000 / 1000433) := by
    rw [show ((1000433 / 1000000) : ℝ) = ((1000000 / 1000433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11606_neg : (433093 / 1000000000) ≤ -Real.log (999567 / 1000000) ∧
    -Real.log (999567 / 1000000) ≤ (216547 / 500000000) := by
  have h := checkLog_sound (w := (433 / 1999567)) (n := 12)
    (lo := (433093 / 1000000000)) (hi := (216547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999567) = 1/(999567 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11606 : Bounds (-216547 / 500000000) (-433093 / 1000000000) (Real.log (999567 / 1000000)) := by
  have h := reflection_log_11606_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11607_neg : (100854941 / 500000000) ≤ -Real.log (1000000 / 1223493) ∧
    -Real.log (1000000 / 1223493) ≤ (201709883 / 1000000000) := by
  have h := checkLog_sound (w := (223493 / 2223493)) (n := 12)
    (lo := (100854941 / 500000000)) (hi := (201709883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1223493 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1223493 / 1000000) = 1/(1000000 / 1223493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11607 : Bounds (100854941 / 500000000) (201709883 / 1000000000) (Real.log (1223493 / 1000000)) := by
  have h := reflection_log_11607_neg
  have he : Real.log (1223493 / 1000000) = -Real.log (1000000 / 1223493) := by
    rw [show ((1223493 / 1000000) : ℝ) = ((1000000 / 1223493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11608_neg : (252949621 / 1000000000) ≤ -Real.log (776507 / 1000000) ∧
    -Real.log (776507 / 1000000) ≤ (126474811 / 500000000) := by
  have h := checkLog_sound (w := (223493 / 1776507)) (n := 12)
    (lo := (252949621 / 1000000000)) (hi := (126474811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 776507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 776507) = 1/(776507 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11608 : Bounds (-126474811 / 500000000) (-252949621 / 1000000000) (Real.log (776507 / 1000000)) := by
  have h := reflection_log_11608_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11609_neg : (20250483 / 100000000) ≤ -Real.log (500000 / 612233) ∧
    -Real.log (500000 / 612233) ≤ (202504831 / 1000000000) := by
  have h := checkLog_sound (w := (112233 / 1112233)) (n := 12)
    (lo := (20250483 / 100000000)) (hi := (202504831 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((612233 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(612233 / 500000) = 1/(500000 / 612233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11609 : Bounds (20250483 / 100000000) (202504831 / 1000000000) (Real.log (612233 / 500000)) := by
  have h := reflection_log_11609_neg
  have he : Real.log (612233 / 500000) = -Real.log (500000 / 612233) := by
    rw [show ((612233 / 500000) : ℝ) = ((500000 / 612233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11610_neg : (127101727 / 500000000) ≤ -Real.log (387767 / 500000) ∧
    -Real.log (387767 / 500000) ≤ (50840691 / 200000000) := by
  have h := checkLog_sound (w := (112233 / 887767)) (n := 12)
    (lo := (127101727 / 500000000)) (hi := (50840691 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 387767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 387767) = 1/(387767 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11610 : Bounds (-50840691 / 200000000) (-127101727 / 500000000) (Real.log (387767 / 500000)) := by
  have h := reflection_log_11610_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11611_neg : (807791 / 15625000) ≤ -Real.log (237403753711 / 250000000000) ∧
    -Real.log (237403753711 / 250000000000) ≤ (413589 / 8000000) := by
  have h := checkLog_sound (w := (12596246289 / 487403753711)) (n := 12)
    (lo := (807791 / 15625000)) (hi := (413589 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 237403753711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 237403753711) = 1/(237403753711 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11611 : Bounds (-413589 / 8000000) (-807791 / 15625000) (Real.log (237403753711 / 250000000000)) := by
  have h := reflection_log_11611_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11612_neg : (51239739 / 1000000000) ≤ -Real.log (950050878951 / 1000000000000) ∧
    -Real.log (950050878951 / 1000000000000) ≤ (2561987 / 50000000) := by
  have h := checkLog_sound (w := (49949121049 / 1950050878951)) (n := 12)
    (lo := (51239739 / 1000000000)) (hi := (2561987 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 950050878951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 950050878951) = 1/(950050878951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11612 : Bounds (-2561987 / 50000000) (-51239739 / 1000000000) (Real.log (950050878951 / 1000000000000)) := by
  have h := reflection_log_11612_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11613_neg : (28416219 / 62500000) ≤ -Real.log (500000000 / 787818397) ∧
    -Real.log (500000000 / 787818397) ≤ (90931901 / 200000000) := by
  have h := checkLog_sound (w := (287818397 / 1287818397)) (n := 12)
    (lo := (28416219 / 62500000)) (hi := (90931901 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((787818397 / 500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(787818397 / 500000000) = 1/(500000000 / 787818397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11613 : Bounds (28416219 / 62500000) (90931901 / 200000000) (Real.log (787818397 / 500000000)) := by
  have h := reflection_log_11613_neg
  have he : Real.log (787818397 / 500000000) = -Real.log (500000000 / 787818397) := by
    rw [show ((787818397 / 500000000) : ℝ) = ((500000000 / 787818397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11614_neg : (91341657 / 200000000) ≤ -Real.log (500000000000 / 789434118943) ∧
    -Real.log (500000000000 / 789434118943) ≤ (228354143 / 500000000) := by
  have h := checkLog_sound (w := (289434118943 / 1289434118943)) (n := 12)
    (lo := (91341657 / 200000000)) (hi := (228354143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((789434118943 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(789434118943 / 500000000000) = 1/(500000000000 / 789434118943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11614 : Bounds (91341657 / 200000000) (228354143 / 500000000) (Real.log (789434118943 / 500000000000)) := by
  have h := reflection_log_11614_neg
  have he : Real.log (789434118943 / 500000000000) = -Real.log (500000000000 / 789434118943) := by
    rw [show ((789434118943 / 500000000000) : ℝ) = ((500000000000 / 789434118943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11615_neg : (115588241 / 125000000) ≤ -Real.log (500000000000 / 1260563380281) ∧
    -Real.log (500000000000 / 1260563380281) ≤ (92470593 / 100000000) := by
  have h := checkLog_sound (w := (260563380281 / 2260563380281)) (n := 12)
    (lo := (57889687 / 250000000)) (hi := (231558749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1260563380281 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1260563380281 / 1000000000000) = 1/(500000000000 / 1260563380281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11615 : Bounds (115588241 / 125000000) (92470593 / 100000000) (Real.log (1260563380281 / 500000000000)) := by
  have h := reflection_log_11615_neg
  have he : Real.log (1260563380281 / 500000000000) = -Real.log (500000000000 / 1260563380281) := by
    rw [show ((1260563380281 / 500000000000) : ℝ) = ((500000000000 / 1260563380281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11616_neg : (927166123 / 1000000000) ≤ -Real.log (976562500 / 2468102403) ∧
    -Real.log (976562500 / 2468102403) ≤ (7417329 / 8000000) := by
  have h := checkLog_sound (w := (514977403 / 4421227403)) (n := 12)
    (lo := (234018943 / 1000000000)) (hi := (1828273 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2468102403 / 1953125000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2468102403 / 1953125000) = 1/(976562500 / 2468102403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11616 : Bounds (927166123 / 1000000000) (7417329 / 8000000) (Real.log (2468102403 / 976562500)) := by
  have h := reflection_log_11616_neg
  have he : Real.log (2468102403 / 976562500) = -Real.log (976562500 / 2468102403) := by
    rw [show ((2468102403 / 976562500) : ℝ) = ((976562500 / 2468102403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11617_neg : (180233871 / 500000000) ≤ -Real.log (500 / 717) ∧
    -Real.log (500 / 717) ≤ (360467743 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 1217)) (n := 12)
    (lo := (180233871 / 500000000)) (hi := (360467743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717 / 500) = 1/(500 / 717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11617 : Bounds (180233871 / 500000000) (360467743 / 1000000000) (Real.log (717 / 500)) := by
  have h := reflection_log_11617_neg
  have he : Real.log (717 / 500) = -Real.log (500 / 717) := by
    rw [show ((717 / 500) : ℝ) = ((500 / 717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11618_neg : (1422903 / 2500000) ≤ -Real.log (283 / 500) ∧
    -Real.log (283 / 500) ≤ (569161201 / 1000000000) := by
  have h := checkLog_sound (w := (217 / 783)) (n := 12)
    (lo := (1422903 / 2500000)) (hi := (569161201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 283) = 1/(283 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11618 : Bounds (-569161201 / 1000000000) (-1422903 / 2500000) (Real.log (283 / 500)) := by
  have h := reflection_log_11618_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11619_neg : (86781 / 200000000) ≤ -Real.log (500000 / 500217) ∧
    -Real.log (500000 / 500217) ≤ (216953 / 500000000) := by
  have h := checkLog_sound (w := (217 / 1000217)) (n := 12)
    (lo := (86781 / 200000000)) (hi := (216953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500217 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500217 / 500000) = 1/(500000 / 500217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11619 : Bounds (86781 / 200000000) (216953 / 500000000) (Real.log (500217 / 500000)) := by
  have h := reflection_log_11619_neg
  have he : Real.log (500217 / 500000) = -Real.log (500000 / 500217) := by
    rw [show ((500217 / 500000) : ℝ) = ((500000 / 500217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11620_neg : (217047 / 500000000) ≤ -Real.log (499783 / 500000) ∧
    -Real.log (499783 / 500000) ≤ (86819 / 200000000) := by
  have h := checkLog_sound (w := (217 / 999783)) (n := 12)
    (lo := (217047 / 500000000)) (hi := (86819 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499783) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499783) = 1/(499783 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11620 : Bounds (-86819 / 200000000) (-217047 / 500000000) (Real.log (499783 / 500000)) := by
  have h := reflection_log_11620_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11621_neg : (202163399 / 1000000000) ≤ -Real.log (62500 / 76503) ∧
    -Real.log (62500 / 76503) ≤ (1010817 / 5000000) := by
  have h := checkLog_sound (w := (14003 / 139003)) (n := 12)
    (lo := (202163399 / 1000000000)) (hi := (1010817 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76503 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76503 / 62500) = 1/(62500 / 76503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11621 : Bounds (202163399 / 1000000000) (1010817 / 5000000) (Real.log (76503 / 62500)) := by
  have h := reflection_log_11621_neg
  have he : Real.log (76503 / 62500) = -Real.log (62500 / 76503) := by
    rw [show ((76503 / 62500) : ℝ) = ((62500 / 76503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11622_neg : (31708077 / 125000000) ≤ -Real.log (48497 / 62500) ∧
    -Real.log (48497 / 62500) ≤ (253664617 / 1000000000) := by
  have h := checkLog_sound (w := (14003 / 110997)) (n := 12)
    (lo := (31708077 / 125000000)) (hi := (253664617 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 48497) = 1/(48497 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11622 : Bounds (-253664617 / 1000000000) (-31708077 / 125000000) (Real.log (48497 / 62500)) := by
  have h := reflection_log_11622_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11623_neg : (202958803 / 1000000000) ≤ -Real.log (500000 / 612511) ∧
    -Real.log (500000 / 612511) ≤ (50739701 / 250000000) := by
  have h := checkLog_sound (w := (112511 / 1112511)) (n := 12)
    (lo := (202958803 / 1000000000)) (hi := (50739701 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((612511 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(612511 / 500000) = 1/(500000 / 612511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11623 : Bounds (202958803 / 1000000000) (50739701 / 250000000) (Real.log (612511 / 500000)) := by
  have h := reflection_log_11623_neg
  have he : Real.log (612511 / 500000) = -Real.log (500000 / 612511) := by
    rw [show ((612511 / 500000) : ℝ) = ((500000 / 612511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11624_neg : (254920637 / 1000000000) ≤ -Real.log (387489 / 500000) ∧
    -Real.log (387489 / 500000) ≤ (127460319 / 500000000) := by
  have h := checkLog_sound (w := (112511 / 887489)) (n := 12)
    (lo := (254920637 / 1000000000)) (hi := (127460319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 387489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 387489) = 1/(387489 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11624 : Bounds (-127460319 / 500000000) (-254920637 / 1000000000) (Real.log (387489 / 500000)) := by
  have h := reflection_log_11624_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11625_neg : (25980917 / 500000000) ≤ -Real.log (237341274879 / 250000000000) ∧
    -Real.log (237341274879 / 250000000000) ≤ (10392367 / 200000000) := by
  have h := checkLog_sound (w := (12658725121 / 487341274879)) (n := 12)
    (lo := (25980917 / 500000000)) (hi := (10392367 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 237341274879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 237341274879) = 1/(237341274879 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11625 : Bounds (-10392367 / 200000000) (-25980917 / 500000000) (Real.log (237341274879 / 250000000000)) := by
  have h := reflection_log_11625_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11626_neg : (51501217 / 1000000000) ≤ -Real.log (3710165991 / 3906250000) ∧
    -Real.log (3710165991 / 3906250000) ≤ (25750609 / 500000000) := by
  have h := checkLog_sound (w := (196084009 / 7616415991)) (n := 12)
    (lo := (51501217 / 1000000000)) (hi := (25750609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3710165991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3710165991) = 1/(3710165991 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11626 : Bounds (-25750609 / 500000000) (-51501217 / 1000000000) (Real.log (3710165991 / 3906250000)) := by
  have h := reflection_log_11626_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11627_neg : (91165603 / 200000000) ≤ -Real.log (25000000000 / 39436975483) ∧
    -Real.log (25000000000 / 39436975483) ≤ (28489251 / 62500000) := by
  have h := checkLog_sound (w := (14436975483 / 64436975483)) (n := 12)
    (lo := (91165603 / 200000000)) (hi := (28489251 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39436975483 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39436975483 / 25000000000) = 1/(25000000000 / 39436975483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11627 : Bounds (91165603 / 200000000) (28489251 / 62500000) (Real.log (39436975483 / 25000000000)) := by
  have h := reflection_log_11627_neg
  have he : Real.log (39436975483 / 25000000000) = -Real.log (25000000000 / 39436975483) := by
    rw [show ((39436975483 / 25000000000) : ℝ) = ((25000000000 / 39436975483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11628_neg : (5723493 / 12500000) ≤ -Real.log (500000000000 / 790359210197) ∧
    -Real.log (500000000000 / 790359210197) ≤ (457879441 / 1000000000) := by
  have h := checkLog_sound (w := (290359210197 / 1290359210197)) (n := 12)
    (lo := (5723493 / 12500000)) (hi := (457879441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((790359210197 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(790359210197 / 500000000000) = 1/(500000000000 / 790359210197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11628 : Bounds (5723493 / 12500000) (457879441 / 1000000000) (Real.log (790359210197 / 500000000000)) := by
  have h := reflection_log_11628_neg
  have he : Real.log (790359210197 / 500000000000) = -Real.log (500000000000 / 790359210197) := by
    rw [show ((790359210197 / 500000000000) : ℝ) = ((500000000000 / 790359210197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11629_neg : (927166123 / 1000000000) ≤ -Real.log (100000000000 / 252733686067) ∧
    -Real.log (100000000000 / 252733686067) ≤ (7417329 / 8000000) := by
  have h := checkLog_sound (w := (52733686067 / 452733686067)) (n := 12)
    (lo := (234018943 / 1000000000)) (hi := (1828273 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((252733686067 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(252733686067 / 200000000000) = 1/(100000000000 / 252733686067) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11629 : Bounds (927166123 / 1000000000) (7417329 / 8000000) (Real.log (252733686067 / 100000000000)) := by
  have h := reflection_log_11629_neg
  have he : Real.log (252733686067 / 100000000000) = -Real.log (100000000000 / 252733686067) := by
    rw [show ((252733686067 / 100000000000) : ℝ) = ((100000000000 / 252733686067) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11630_neg : (464814471 / 500000000) ≤ -Real.log (500000000000 / 1266784452297) ∧
    -Real.log (500000000000 / 1266784452297) ≤ (58101809 / 62500000) := by
  have h := checkLog_sound (w := (266784452297 / 2266784452297)) (n := 12)
    (lo := (118240881 / 500000000)) (hi := (236481763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1266784452297 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1266784452297 / 1000000000000) = 1/(500000000000 / 1266784452297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11630 : Bounds (464814471 / 500000000) (58101809 / 62500000) (Real.log (1266784452297 / 500000000000)) := by
  have h := reflection_log_11630_neg
  have he : Real.log (1266784452297 / 500000000000) = -Real.log (500000000000 / 1266784452297) := by
    rw [show ((1266784452297 / 500000000000) : ℝ) = ((500000000000 / 1266784452297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11631_neg : (361164849 / 1000000000) ≤ -Real.log (200 / 287) ∧
    -Real.log (200 / 287) ≤ (7223297 / 20000000) := by
  have h := checkLog_sound (w := (87 / 487)) (n := 12)
    (lo := (361164849 / 1000000000)) (hi := (7223297 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((287 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(287 / 200) = 1/(200 / 287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11631 : Bounds (361164849 / 1000000000) (7223297 / 20000000) (Real.log (287 / 200)) := by
  have h := reflection_log_11631_neg
  have he : Real.log (287 / 200) = -Real.log (200 / 287) := by
    rw [show ((287 / 200) : ℝ) = ((200 / 287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11632_neg : (570929547 / 1000000000) ≤ -Real.log (113 / 200) ∧
    -Real.log (113 / 200) ≤ (142732387 / 250000000) := by
  have h := checkLog_sound (w := (87 / 313)) (n := 12)
    (lo := (570929547 / 1000000000)) (hi := (142732387 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 113) = 1/(113 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11632 : Bounds (-142732387 / 250000000) (-570929547 / 1000000000) (Real.log (113 / 200)) := by
  have h := reflection_log_11632_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11633_neg : (86981 / 200000000) ≤ -Real.log (200000 / 200087) ∧
    -Real.log (200000 / 200087) ≤ (217453 / 500000000) := by
  have h := checkLog_sound (w := (87 / 400087)) (n := 12)
    (lo := (86981 / 200000000)) (hi := (217453 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200087 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200087 / 200000) = 1/(200000 / 200087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11633 : Bounds (86981 / 200000000) (217453 / 500000000) (Real.log (200087 / 200000)) := by
  have h := reflection_log_11633_neg
  have he : Real.log (200087 / 200000) = -Real.log (200000 / 200087) := by
    rw [show ((200087 / 200000) : ℝ) = ((200000 / 200087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11634_neg : (217547 / 500000000) ≤ -Real.log (199913 / 200000) ∧
    -Real.log (199913 / 200000) ≤ (87019 / 200000000) := by
  have h := checkLog_sound (w := (87 / 399913)) (n := 12)
    (lo := (217547 / 500000000)) (hi := (87019 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199913) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199913) = 1/(199913 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11634 : Bounds (-87019 / 200000000) (-217547 / 500000000) (Real.log (199913 / 200000)) := by
  have h := reflection_log_11634_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11635_neg : (101308763 / 500000000) ≤ -Real.log (250000 / 306151) ∧
    -Real.log (250000 / 306151) ≤ (202617527 / 1000000000) := by
  have h := checkLog_sound (w := (56151 / 556151)) (n := 12)
    (lo := (101308763 / 500000000)) (hi := (202617527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((306151 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(306151 / 250000) = 1/(250000 / 306151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11635 : Bounds (101308763 / 500000000) (202617527 / 1000000000) (Real.log (306151 / 250000)) := by
  have h := reflection_log_11635_neg
  have he : Real.log (306151 / 250000) = -Real.log (250000 / 306151) := by
    rw [show ((306151 / 250000) : ℝ) = ((250000 / 306151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11636_neg : (63595353 / 250000000) ≤ -Real.log (193849 / 250000) ∧
    -Real.log (193849 / 250000) ≤ (254381413 / 1000000000) := by
  have h := checkLog_sound (w := (56151 / 443849)) (n := 12)
    (lo := (63595353 / 250000000)) (hi := (254381413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 193849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 193849) = 1/(193849 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11636 : Bounds (-254381413 / 1000000000) (-63595353 / 250000000) (Real.log (193849 / 250000)) := by
  have h := reflection_log_11636_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11637_neg : (40682677 / 200000000) ≤ -Real.log (1000000 / 1225579) ∧
    -Real.log (1000000 / 1225579) ≤ (101706693 / 500000000) := by
  have h := checkLog_sound (w := (225579 / 2225579)) (n := 12)
    (lo := (40682677 / 200000000)) (hi := (101706693 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1225579 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1225579 / 1000000) = 1/(1000000 / 1225579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11637 : Bounds (40682677 / 200000000) (101706693 / 500000000) (Real.log (1225579 / 1000000)) := by
  have h := reflection_log_11637_neg
  have he : Real.log (1225579 / 1000000) = -Real.log (1000000 / 1225579) := by
    rw [show ((1225579 / 1000000) : ℝ) = ((1000000 / 1225579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11638_neg : (2045117 / 8000000) ≤ -Real.log (774421 / 1000000) ∧
    -Real.log (774421 / 1000000) ≤ (127819813 / 500000000) := by
  have h := checkLog_sound (w := (225579 / 1774421)) (n := 12)
    (lo := (2045117 / 8000000)) (hi := (127819813 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 774421) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 774421) = 1/(774421 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11638 : Bounds (-127819813 / 500000000) (-2045117 / 8000000) (Real.log (774421 / 1000000)) := by
  have h := reflection_log_11638_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11639_neg : (163207 / 3125000) ≤ -Real.log (949114114759 / 1000000000000) ∧
    -Real.log (949114114759 / 1000000000000) ≤ (52226241 / 1000000000) := by
  have h := checkLog_sound (w := (50885885241 / 1949114114759)) (n := 12)
    (lo := (163207 / 3125000)) (hi := (52226241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 949114114759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 949114114759) = 1/(949114114759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11639 : Bounds (-52226241 / 1000000000) (-163207 / 3125000) (Real.log (949114114759 / 1000000000000)) := by
  have h := reflection_log_11639_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11640_neg : (10352777 / 200000000) ≤ -Real.log (59347065199 / 62500000000) ∧
    -Real.log (59347065199 / 62500000000) ≤ (25881943 / 500000000) := by
  have h := checkLog_sound (w := (3152934801 / 121847065199)) (n := 12)
    (lo := (10352777 / 200000000)) (hi := (25881943 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59347065199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59347065199) = 1/(59347065199 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11640 : Bounds (-25881943 / 500000000) (-10352777 / 200000000) (Real.log (59347065199 / 62500000000)) := by
  have h := reflection_log_11640_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11641_neg : (228499469 / 500000000) ≤ -Real.log (100000000000 / 157932720829) ∧
    -Real.log (100000000000 / 157932720829) ≤ (456998939 / 1000000000) := by
  have h := checkLog_sound (w := (57932720829 / 257932720829)) (n := 12)
    (lo := (228499469 / 500000000)) (hi := (456998939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157932720829 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157932720829 / 100000000000) = 1/(100000000000 / 157932720829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11641 : Bounds (228499469 / 500000000) (456998939 / 1000000000) (Real.log (157932720829 / 100000000000)) := by
  have h := reflection_log_11641_neg
  have he : Real.log (157932720829 / 100000000000) = -Real.log (100000000000 / 157932720829) := by
    rw [show ((157932720829 / 100000000000) : ℝ) = ((100000000000 / 157932720829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11642_neg : (459053011 / 1000000000) ≤ -Real.log (25000000000 / 39564364861) ∧
    -Real.log (25000000000 / 39564364861) ≤ (114763253 / 250000000) := by
  have h := checkLog_sound (w := (14564364861 / 64564364861)) (n := 12)
    (lo := (459053011 / 1000000000)) (hi := (114763253 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39564364861 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39564364861 / 25000000000) = 1/(25000000000 / 39564364861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11642 : Bounds (459053011 / 1000000000) (114763253 / 250000000) (Real.log (39564364861 / 25000000000)) := by
  have h := reflection_log_11642_neg
  have he : Real.log (39564364861 / 25000000000) = -Real.log (25000000000 / 39564364861) := by
    rw [show ((39564364861 / 25000000000) : ℝ) = ((25000000000 / 39564364861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11643_neg : (464814471 / 500000000) ≤ -Real.log (62500000000 / 158348056537) ∧
    -Real.log (62500000000 / 158348056537) ≤ (58101809 / 62500000) := by
  have h := checkLog_sound (w := (33348056537 / 283348056537)) (n := 12)
    (lo := (118240881 / 500000000)) (hi := (236481763 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((158348056537 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(158348056537 / 125000000000) = 1/(62500000000 / 158348056537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11643 : Bounds (464814471 / 500000000) (58101809 / 62500000) (Real.log (158348056537 / 62500000000)) := by
  have h := reflection_log_11643_neg
  have he : Real.log (158348056537 / 62500000000) = -Real.log (62500000000 / 158348056537) := by
    rw [show ((158348056537 / 62500000000) : ℝ) = ((62500000000 / 158348056537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11644_neg : (233023599 / 250000000) ≤ -Real.log (20000000000 / 50796460177) ∧
    -Real.log (20000000000 / 50796460177) ≤ (466047199 / 500000000) := by
  have h := checkLog_sound (w := (10796460177 / 90796460177)) (n := 12)
    (lo := (14934201 / 62500000)) (hi := (238947217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50796460177 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50796460177 / 40000000000) = 1/(20000000000 / 50796460177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11644 : Bounds (233023599 / 250000000) (466047199 / 500000000) (Real.log (50796460177 / 20000000000)) := by
  have h := reflection_log_11644_neg
  have he : Real.log (50796460177 / 20000000000) = -Real.log (20000000000 / 50796460177) := by
    rw [show ((50796460177 / 20000000000) : ℝ) = ((20000000000 / 50796460177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11645_neg : (36186147 / 100000000) ≤ -Real.log (250 / 359) ∧
    -Real.log (250 / 359) ≤ (361861471 / 1000000000) := by
  have h := checkLog_sound (w := (109 / 609)) (n := 12)
    (lo := (36186147 / 100000000)) (hi := (361861471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359 / 250) = 1/(250 / 359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11645 : Bounds (36186147 / 100000000) (361861471 / 1000000000) (Real.log (359 / 250)) := by
  have h := reflection_log_11645_neg
  have he : Real.log (359 / 250) = -Real.log (250 / 359) := by
    rw [show ((359 / 250) : ℝ) = ((250 / 359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11646_neg : (572701027 / 1000000000) ≤ -Real.log (141 / 250) ∧
    -Real.log (141 / 250) ≤ (143175257 / 250000000) := by
  have h := checkLog_sound (w := (109 / 391)) (n := 12)
    (lo := (572701027 / 1000000000)) (hi := (143175257 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 141) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 141) = 1/(141 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11646 : Bounds (-143175257 / 250000000) (-572701027 / 1000000000) (Real.log (141 / 250)) := by
  have h := reflection_log_11646_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11647_neg : (6811 / 15625000) ≤ -Real.log (250000 / 250109) ∧
    -Real.log (250000 / 250109) ≤ (87181 / 200000000) := by
  have h := checkLog_sound (w := (109 / 500109)) (n := 12)
    (lo := (6811 / 15625000)) (hi := (87181 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250109 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250109 / 250000) = 1/(250000 / 250109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11647 : Bounds (6811 / 15625000) (87181 / 200000000) (Real.log (250109 / 250000)) := by
  have h := reflection_log_11647_neg
  have he : Real.log (250109 / 250000) = -Real.log (250000 / 250109) := by
    rw [show ((250109 / 250000) : ℝ) = ((250000 / 250109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
