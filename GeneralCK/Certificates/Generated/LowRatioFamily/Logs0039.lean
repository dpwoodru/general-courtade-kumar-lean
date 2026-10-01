import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2496_neg : (88117807 / 1000000000) ≤ -Real.log (915653 / 1000000) ∧
    -Real.log (915653 / 1000000) ≤ (5507363 / 62500000) := by
  have h := checkLog_sound (w := (84347 / 1915653)) (n := 12)
    (lo := (88117807 / 1000000000)) (hi := (5507363 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915653) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915653) = 1/(915653 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2496 : Bounds (-5507363 / 62500000) (-88117807 / 1000000000) (Real.log (915653 / 1000000)) := by
  have h := reflection_log_2496_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2497_neg : (40589953 / 500000000) ≤ -Real.log (500000 / 542283) ∧
    -Real.log (500000 / 542283) ≤ (81179907 / 1000000000) := by
  have h := checkLog_sound (w := (42283 / 1042283)) (n := 12)
    (lo := (40589953 / 500000000)) (hi := (81179907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542283 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542283 / 500000) = 1/(500000 / 542283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2497 : Bounds (40589953 / 500000000) (81179907 / 1000000000) (Real.log (542283 / 500000)) := by
  have h := reflection_log_2497_neg
  have he : Real.log (542283 / 500000) = -Real.log (500000 / 542283) := by
    rw [show ((542283 / 500000) : ℝ) = ((500000 / 542283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2498_neg : (88357009 / 1000000000) ≤ -Real.log (457717 / 500000) ∧
    -Real.log (457717 / 500000) ≤ (8835701 / 100000000) := by
  have h := checkLog_sound (w := (42283 / 957717)) (n := 12)
    (lo := (88357009 / 1000000000)) (hi := (8835701 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457717) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457717) = 1/(457717 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2498 : Bounds (-8835701 / 100000000) (-88357009 / 1000000000) (Real.log (457717 / 500000)) := by
  have h := reflection_log_2498_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2499_neg : (3588551 / 500000000) ≤ -Real.log (248212147911 / 250000000000) ∧
    -Real.log (248212147911 / 250000000000) ≤ (7177103 / 1000000000) := by
  have h := checkLog_sound (w := (1787852089 / 498212147911)) (n := 12)
    (lo := (3588551 / 500000000)) (hi := (7177103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248212147911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248212147911) = 1/(248212147911 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2499 : Bounds (-7177103 / 1000000000) (-3588551 / 500000000) (Real.log (248212147911 / 250000000000)) := by
  have h := reflection_log_2499_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2500_neg : (1784961 / 250000000) ≤ -Real.log (992885583591 / 1000000000000) ∧
    -Real.log (992885583591 / 1000000000000) ≤ (1427969 / 200000000) := by
  have h := checkLog_sound (w := (7114416409 / 1992885583591)) (n := 12)
    (lo := (1784961 / 250000000)) (hi := (1427969 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992885583591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992885583591) = 1/(992885583591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2500 : Bounds (-1427969 / 200000000) (-1784961 / 250000000) (Real.log (992885583591 / 1000000000000)) := by
  have h := reflection_log_2500_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2501_neg : (169095769 / 1000000000) ≤ -Real.log (500000000000 / 592116773493) ∧
    -Real.log (500000000000 / 592116773493) ≤ (16909577 / 100000000) := by
  have h := checkLog_sound (w := (92116773493 / 1092116773493)) (n := 12)
    (lo := (169095769 / 1000000000)) (hi := (16909577 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592116773493 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592116773493 / 500000000000) = 1/(500000000000 / 592116773493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2501 : Bounds (169095769 / 1000000000) (16909577 / 100000000) (Real.log (592116773493 / 500000000000)) := by
  have h := reflection_log_2501_neg
  have he : Real.log (592116773493 / 500000000000) = -Real.log (500000000000 / 592116773493) := by
    rw [show ((592116773493 / 500000000000) : ℝ) = ((500000000000 / 592116773493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2502_neg : (42384229 / 250000000) ≤ -Real.log (250000000000 / 296189020727) ∧
    -Real.log (250000000000 / 296189020727) ≤ (169536917 / 1000000000) := by
  have h := checkLog_sound (w := (46189020727 / 546189020727)) (n := 12)
    (lo := (42384229 / 250000000)) (hi := (169536917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296189020727 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296189020727 / 250000000000) = 1/(250000000000 / 296189020727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2502 : Bounds (42384229 / 250000000) (169536917 / 1000000000) (Real.log (296189020727 / 250000000000)) := by
  have h := reflection_log_2502_neg
  have he : Real.log (296189020727 / 250000000000) = -Real.log (250000000000 / 296189020727) := by
    rw [show ((296189020727 / 250000000000) : ℝ) = ((250000000000 / 296189020727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2503_neg : (169607861 / 500000000) ≤ -Real.log (500000000000 / 701923076923) ∧
    -Real.log (500000000000 / 701923076923) ≤ (339215723 / 1000000000) := by
  have h := checkLog_sound (w := (201923076923 / 1201923076923)) (n := 12)
    (lo := (169607861 / 500000000)) (hi := (339215723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((701923076923 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(701923076923 / 500000000000) = 1/(500000000000 / 701923076923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2503 : Bounds (169607861 / 500000000) (339215723 / 1000000000) (Real.log (701923076923 / 500000000000)) := by
  have h := reflection_log_2503_neg
  have he : Real.log (701923076923 / 500000000000) = -Real.log (500000000000 / 701923076923) := by
    rw [show ((701923076923 / 500000000000) : ℝ) = ((500000000000 / 701923076923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2504_neg : (169710767 / 500000000) ≤ -Real.log (500000000000 / 702067556197) ∧
    -Real.log (500000000000 / 702067556197) ≤ (67884307 / 200000000) := by
  have h := checkLog_sound (w := (202067556197 / 1202067556197)) (n := 12)
    (lo := (169710767 / 500000000)) (hi := (67884307 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((702067556197 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(702067556197 / 500000000000) = 1/(500000000000 / 702067556197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2504 : Bounds (169710767 / 500000000) (67884307 / 200000000) (Real.log (702067556197 / 500000000000)) := by
  have h := reflection_log_2504_neg
  have he : Real.log (702067556197 / 500000000000) = -Real.log (500000000000 / 702067556197) := by
    rw [show ((702067556197 / 500000000000) : ℝ) = ((500000000000 / 702067556197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2505_neg : (77732051 / 500000000) ≤ -Real.log (5000 / 5841) ∧
    -Real.log (5000 / 5841) ≤ (155464103 / 1000000000) := by
  have h := checkLog_sound (w := (841 / 10841)) (n := 12)
    (lo := (77732051 / 500000000)) (hi := (155464103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5841 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5841 / 5000) = 1/(5000 / 5841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2505 : Bounds (77732051 / 500000000) (155464103 / 1000000000) (Real.log (5841 / 5000)) := by
  have h := reflection_log_2505_neg
  have he : Real.log (5841 / 5000) = -Real.log (5000 / 5841) := by
    rw [show ((5841 / 5000) : ℝ) = ((5000 / 5841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2506_neg : (184163251 / 1000000000) ≤ -Real.log (4159 / 5000) ∧
    -Real.log (4159 / 5000) ≤ (46040813 / 250000000) := by
  have h := checkLog_sound (w := (841 / 9159)) (n := 12)
    (lo := (184163251 / 1000000000)) (hi := (46040813 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4159) = 1/(4159 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2506 : Bounds (-46040813 / 250000000) (-184163251 / 1000000000) (Real.log (4159 / 5000)) := by
  have h := reflection_log_2506_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2507_neg : (33637 / 200000000) ≤ -Real.log (5000000 / 5000841) ∧
    -Real.log (5000000 / 5000841) ≤ (84093 / 500000000) := by
  have h := checkLog_sound (w := (841 / 10000841)) (n := 12)
    (lo := (33637 / 200000000)) (hi := (84093 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000841 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000841 / 5000000) = 1/(5000000 / 5000841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2507 : Bounds (33637 / 200000000) (84093 / 500000000) (Real.log (5000841 / 5000000)) := by
  have h := reflection_log_2507_neg
  have he : Real.log (5000841 / 5000000) = -Real.log (5000000 / 5000841) := by
    rw [show ((5000841 / 5000000) : ℝ) = ((5000000 / 5000841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2508_neg : (84107 / 500000000) ≤ -Real.log (4999159 / 5000000) ∧
    -Real.log (4999159 / 5000000) ≤ (33643 / 200000000) := by
  have h := checkLog_sound (w := (841 / 9999159)) (n := 12)
    (lo := (84107 / 500000000)) (hi := (33643 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999159) = 1/(4999159 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2508 : Bounds (-33643 / 200000000) (-84107 / 500000000) (Real.log (4999159 / 5000000)) := by
  have h := reflection_log_2508_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2509_neg : (40512497 / 500000000) ≤ -Real.log (500000 / 542199) ∧
    -Real.log (500000 / 542199) ≤ (16204999 / 200000000) := by
  have h := checkLog_sound (w := (42199 / 1042199)) (n := 12)
    (lo := (40512497 / 500000000)) (hi := (16204999 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542199 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542199 / 500000) = 1/(500000 / 542199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2509 : Bounds (40512497 / 500000000) (16204999 / 200000000) (Real.log (542199 / 500000)) := by
  have h := reflection_log_2509_neg
  have he : Real.log (542199 / 500000) = -Real.log (500000 / 542199) := by
    rw [show ((542199 / 500000) : ℝ) = ((500000 / 542199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2510_neg : (44086753 / 500000000) ≤ -Real.log (457801 / 500000) ∧
    -Real.log (457801 / 500000) ≤ (88173507 / 1000000000) := by
  have h := checkLog_sound (w := (42199 / 957801)) (n := 12)
    (lo := (44086753 / 500000000)) (hi := (88173507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457801) = 1/(457801 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2510 : Bounds (-88173507 / 1000000000) (-44086753 / 500000000) (Real.log (457801 / 500000)) := by
  have h := reflection_log_2510_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2511_neg : (81226929 / 1000000000) ≤ -Real.log (1000000 / 1084617) ∧
    -Real.log (1000000 / 1084617) ≤ (8122693 / 100000000) := by
  have h := checkLog_sound (w := (84617 / 2084617)) (n := 12)
    (lo := (81226929 / 1000000000)) (hi := (8122693 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084617 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084617 / 1000000) = 1/(1000000 / 1084617) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2511 : Bounds (81226929 / 1000000000) (8122693 / 100000000) (Real.log (1084617 / 1000000)) := by
  have h := reflection_log_2511_neg
  have he : Real.log (1084617 / 1000000) = -Real.log (1000000 / 1084617) := by
    rw [show ((1084617 / 1000000) : ℝ) = ((1000000 / 1084617) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2512_neg : (44206361 / 500000000) ≤ -Real.log (915383 / 1000000) ∧
    -Real.log (915383 / 1000000) ≤ (88412723 / 1000000000) := by
  have h := checkLog_sound (w := (84617 / 1915383)) (n := 12)
    (lo := (44206361 / 500000000)) (hi := (88412723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915383) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915383) = 1/(915383 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2512 : Bounds (-88412723 / 1000000000) (-44206361 / 500000000) (Real.log (915383 / 1000000)) := by
  have h := reflection_log_2512_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2513_neg : (56139 / 7812500) ≤ -Real.log (992839963311 / 1000000000000) ∧
    -Real.log (992839963311 / 1000000000000) ≤ (7185793 / 1000000000) := by
  have h := checkLog_sound (w := (7160036689 / 1992839963311)) (n := 12)
    (lo := (56139 / 7812500)) (hi := (7185793 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992839963311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992839963311) = 1/(992839963311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2513 : Bounds (-7185793 / 1000000000) (-56139 / 7812500) (Real.log (992839963311 / 1000000000000)) := by
  have h := reflection_log_2513_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2514_neg : (223391 / 31250000) ≤ -Real.log (248219244399 / 250000000000) ∧
    -Real.log (248219244399 / 250000000000) ≤ (7148513 / 1000000000) := by
  have h := checkLog_sound (w := (1780755601 / 498219244399)) (n := 12)
    (lo := (223391 / 31250000)) (hi := (7148513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248219244399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248219244399) = 1/(248219244399 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2514 : Bounds (-7148513 / 1000000000) (-223391 / 31250000) (Real.log (248219244399 / 250000000000)) := by
  have h := reflection_log_2514_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2515_neg : (338397 / 2000000) ≤ -Real.log (500000000000 / 592177605553) ∧
    -Real.log (500000000000 / 592177605553) ≤ (169198501 / 1000000000) := by
  have h := checkLog_sound (w := (92177605553 / 1092177605553)) (n := 12)
    (lo := (338397 / 2000000)) (hi := (169198501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592177605553 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592177605553 / 500000000000) = 1/(500000000000 / 592177605553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2515 : Bounds (338397 / 2000000) (169198501 / 1000000000) (Real.log (592177605553 / 500000000000)) := by
  have h := reflection_log_2515_neg
  have he : Real.log (592177605553 / 500000000000) = -Real.log (500000000000 / 592177605553) := by
    rw [show ((592177605553 / 500000000000) : ℝ) = ((500000000000 / 592177605553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2516_neg : (169639651 / 1000000000) ≤ -Real.log (15625000000 / 18513715707) ∧
    -Real.log (15625000000 / 18513715707) ≤ (42409913 / 250000000) := by
  have h := checkLog_sound (w := (2888715707 / 34138715707)) (n := 12)
    (lo := (169639651 / 1000000000)) (hi := (42409913 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18513715707 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18513715707 / 15625000000) = 1/(15625000000 / 18513715707) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2516 : Bounds (169639651 / 1000000000) (42409913 / 250000000) (Real.log (18513715707 / 15625000000)) := by
  have h := reflection_log_2516_neg
  have he : Real.log (18513715707 / 15625000000) = -Real.log (15625000000 / 18513715707) := by
    rw [show ((18513715707 / 15625000000) : ℝ) = ((15625000000 / 18513715707) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2517_neg : (169710767 / 500000000) ≤ -Real.log (125000000000 / 175516889049) ∧
    -Real.log (125000000000 / 175516889049) ≤ (67884307 / 200000000) := by
  have h := checkLog_sound (w := (50516889049 / 300516889049)) (n := 12)
    (lo := (169710767 / 500000000)) (hi := (67884307 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((175516889049 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(175516889049 / 125000000000) = 1/(125000000000 / 175516889049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2517 : Bounds (169710767 / 500000000) (67884307 / 200000000) (Real.log (175516889049 / 125000000000)) := by
  have h := reflection_log_2517_neg
  have he : Real.log (175516889049 / 125000000000) = -Real.log (125000000000 / 175516889049) := by
    rw [show ((175516889049 / 125000000000) : ℝ) = ((125000000000 / 175516889049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2518_neg : (169813677 / 500000000) ≤ -Real.log (50000000000 / 70221207021) ∧
    -Real.log (50000000000 / 70221207021) ≤ (67925471 / 200000000) := by
  have h := checkLog_sound (w := (20221207021 / 120221207021)) (n := 12)
    (lo := (169813677 / 500000000)) (hi := (67925471 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70221207021 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(70221207021 / 50000000000) = 1/(50000000000 / 70221207021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2518 : Bounds (169813677 / 500000000) (67925471 / 200000000) (Real.log (70221207021 / 50000000000)) := by
  have h := reflection_log_2518_neg
  have he : Real.log (70221207021 / 50000000000) = -Real.log (50000000000 / 70221207021) := by
    rw [show ((70221207021 / 50000000000) : ℝ) = ((50000000000 / 70221207021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2519_neg : (1555497 / 10000000) ≤ -Real.log (10000 / 11683) ∧
    -Real.log (10000 / 11683) ≤ (155549701 / 1000000000) := by
  have h := checkLog_sound (w := (1683 / 21683)) (n := 12)
    (lo := (1555497 / 10000000)) (hi := (155549701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11683 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11683 / 10000) = 1/(10000 / 11683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2519 : Bounds (1555497 / 10000000) (155549701 / 1000000000) (Real.log (11683 / 10000)) := by
  have h := reflection_log_2519_neg
  have he : Real.log (11683 / 10000) = -Real.log (10000 / 11683) := by
    rw [show ((11683 / 10000) : ℝ) = ((10000 / 11683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2520_neg : (4607087 / 25000000) ≤ -Real.log (8317 / 10000) ∧
    -Real.log (8317 / 10000) ≤ (184283481 / 1000000000) := by
  have h := checkLog_sound (w := (1683 / 18317)) (n := 12)
    (lo := (4607087 / 25000000)) (hi := (184283481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8317) = 1/(8317 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2520 : Bounds (-184283481 / 1000000000) (-4607087 / 25000000) (Real.log (8317 / 10000)) := by
  have h := reflection_log_2520_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2521_neg : (33657 / 200000000) ≤ -Real.log (10000000 / 10001683) ∧
    -Real.log (10000000 / 10001683) ≤ (84143 / 500000000) := by
  have h := checkLog_sound (w := (1683 / 20001683)) (n := 12)
    (lo := (33657 / 200000000)) (hi := (84143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001683 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001683 / 10000000) = 1/(10000000 / 10001683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2521 : Bounds (33657 / 200000000) (84143 / 500000000) (Real.log (10001683 / 10000000)) := by
  have h := reflection_log_2521_neg
  have he : Real.log (10001683 / 10000000) = -Real.log (10000000 / 10001683) := by
    rw [show ((10001683 / 10000000) : ℝ) = ((10000000 / 10001683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2522_neg : (84157 / 500000000) ≤ -Real.log (9998317 / 10000000) ∧
    -Real.log (9998317 / 10000000) ≤ (33663 / 200000000) := by
  have h := checkLog_sound (w := (1683 / 19998317)) (n := 12)
    (lo := (84157 / 500000000)) (hi := (33663 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998317) = 1/(9998317 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2522 : Bounds (-33663 / 200000000) (-84157 / 500000000) (Real.log (9998317 / 10000000)) := by
  have h := reflection_log_2522_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2523_neg : (81071101 / 1000000000) ≤ -Real.log (31250 / 33889) ∧
    -Real.log (31250 / 33889) ≤ (40535551 / 500000000) := by
  have h := checkLog_sound (w := (2639 / 65139)) (n := 12)
    (lo := (81071101 / 1000000000)) (hi := (40535551 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33889 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(33889 / 31250) = 1/(31250 / 33889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2523 : Bounds (81071101 / 1000000000) (40535551 / 500000000) (Real.log (33889 / 31250)) := by
  have h := reflection_log_2523_neg
  have he : Real.log (33889 / 31250) = -Real.log (31250 / 33889) := by
    rw [show ((33889 / 31250) : ℝ) = ((31250 / 33889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2524_neg : (22057029 / 250000000) ≤ -Real.log (28611 / 31250) ∧
    -Real.log (28611 / 31250) ≤ (88228117 / 1000000000) := by
  have h := checkLog_sound (w := (2639 / 59861)) (n := 12)
    (lo := (22057029 / 250000000)) (hi := (88228117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 28611) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 28611) = 1/(28611 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2524 : Bounds (-88228117 / 1000000000) (-22057029 / 250000000) (Real.log (28611 / 31250)) := by
  have h := reflection_log_2524_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2525_neg : (81273949 / 1000000000) ≤ -Real.log (250000 / 271167) ∧
    -Real.log (250000 / 271167) ≤ (1625479 / 20000000) := by
  have h := checkLog_sound (w := (21167 / 521167)) (n := 12)
    (lo := (81273949 / 1000000000)) (hi := (1625479 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271167 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271167 / 250000) = 1/(250000 / 271167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2525 : Bounds (81273949 / 1000000000) (1625479 / 20000000) (Real.log (271167 / 250000)) := by
  have h := reflection_log_2525_neg
  have he : Real.log (271167 / 250000) = -Real.log (250000 / 271167) := by
    rw [show ((271167 / 250000) : ℝ) = ((250000 / 271167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2526_neg : (88468437 / 1000000000) ≤ -Real.log (228833 / 250000) ∧
    -Real.log (228833 / 250000) ≤ (44234219 / 500000000) := by
  have h := checkLog_sound (w := (21167 / 478833)) (n := 12)
    (lo := (88468437 / 1000000000)) (hi := (44234219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 228833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 228833) = 1/(228833 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2526 : Bounds (-44234219 / 500000000) (-88468437 / 1000000000) (Real.log (228833 / 250000)) := by
  have h := reflection_log_2526_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2527_neg : (899311 / 125000000) ≤ -Real.log (62051958111 / 62500000000) ∧
    -Real.log (62051958111 / 62500000000) ≤ (7194489 / 1000000000) := by
  have h := checkLog_sound (w := (448041889 / 124551958111)) (n := 12)
    (lo := (899311 / 125000000)) (hi := (7194489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62051958111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62051958111) = 1/(62051958111 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2527 : Bounds (-7194489 / 1000000000) (-899311 / 125000000) (Real.log (62051958111 / 62500000000)) := by
  have h := reflection_log_2527_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2528_neg : (1431403 / 200000000) ≤ -Real.log (969598179 / 976562500) ∧
    -Real.log (969598179 / 976562500) ≤ (894627 / 125000000) := by
  have h := checkLog_sound (w := (6964321 / 1946160679)) (n := 12)
    (lo := (1431403 / 200000000)) (hi := (894627 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 969598179) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 969598179) = 1/(969598179 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2528 : Bounds (-894627 / 125000000) (-1431403 / 200000000) (Real.log (969598179 / 976562500)) := by
  have h := reflection_log_2528_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2529_neg : (84649609 / 500000000) ≤ -Real.log (250000000000 / 296118625703) ∧
    -Real.log (250000000000 / 296118625703) ≤ (169299219 / 1000000000) := by
  have h := checkLog_sound (w := (46118625703 / 546118625703)) (n := 12)
    (lo := (84649609 / 500000000)) (hi := (169299219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296118625703 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296118625703 / 250000000000) = 1/(250000000000 / 296118625703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2529 : Bounds (84649609 / 500000000) (169299219 / 1000000000) (Real.log (296118625703 / 250000000000)) := by
  have h := reflection_log_2529_neg
  have he : Real.log (296118625703 / 250000000000) = -Real.log (250000000000 / 296118625703) := by
    rw [show ((296118625703 / 250000000000) : ℝ) = ((250000000000 / 296118625703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2530_neg : (169742387 / 1000000000) ≤ -Real.log (31250000000 / 37031235661) ∧
    -Real.log (31250000000 / 37031235661) ≤ (42435597 / 250000000) := by
  have h := checkLog_sound (w := (5781235661 / 68281235661)) (n := 12)
    (lo := (169742387 / 1000000000)) (hi := (42435597 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37031235661 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37031235661 / 31250000000) = 1/(31250000000 / 37031235661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2530 : Bounds (169742387 / 1000000000) (42435597 / 250000000) (Real.log (37031235661 / 31250000000)) := by
  have h := reflection_log_2530_neg
  have he : Real.log (37031235661 / 31250000000) = -Real.log (31250000000 / 37031235661) := by
    rw [show ((37031235661 / 31250000000) : ℝ) = ((31250000000 / 37031235661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2531_neg : (169813677 / 500000000) ≤ -Real.log (500000000000 / 702212070209) ∧
    -Real.log (500000000000 / 702212070209) ≤ (67925471 / 200000000) := by
  have h := checkLog_sound (w := (202212070209 / 1202212070209)) (n := 12)
    (lo := (169813677 / 500000000)) (hi := (67925471 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((702212070209 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(702212070209 / 500000000000) = 1/(500000000000 / 702212070209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2531 : Bounds (169813677 / 500000000) (67925471 / 200000000) (Real.log (702212070209 / 500000000000)) := by
  have h := reflection_log_2531_neg
  have he : Real.log (702212070209 / 500000000000) = -Real.log (500000000000 / 702212070209) := by
    rw [show ((702212070209 / 500000000000) : ℝ) = ((500000000000 / 702212070209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2532_neg : (16991659 / 50000000) ≤ -Real.log (250000000000 / 351178309487) ∧
    -Real.log (250000000000 / 351178309487) ≤ (339833181 / 1000000000) := by
  have h := checkLog_sound (w := (101178309487 / 601178309487)) (n := 12)
    (lo := (16991659 / 50000000)) (hi := (339833181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351178309487 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351178309487 / 250000000000) = 1/(250000000000 / 351178309487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2532 : Bounds (16991659 / 50000000) (339833181 / 1000000000) (Real.log (351178309487 / 250000000000)) := by
  have h := reflection_log_2532_neg
  have he : Real.log (351178309487 / 250000000000) = -Real.log (250000000000 / 351178309487) := by
    rw [show ((351178309487 / 250000000000) : ℝ) = ((250000000000 / 351178309487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2533_neg : (155635291 / 1000000000) ≤ -Real.log (2500 / 2921) ∧
    -Real.log (2500 / 2921) ≤ (38908823 / 250000000) := by
  have h := checkLog_sound (w := (421 / 5421)) (n := 12)
    (lo := (155635291 / 1000000000)) (hi := (38908823 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2921 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2921 / 2500) = 1/(2500 / 2921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2533 : Bounds (155635291 / 1000000000) (38908823 / 250000000) (Real.log (2921 / 2500)) := by
  have h := reflection_log_2533_neg
  have he : Real.log (2921 / 2500) = -Real.log (2500 / 2921) := by
    rw [show ((2921 / 2500) : ℝ) = ((2500 / 2921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2534_neg : (92201861 / 500000000) ≤ -Real.log (2079 / 2500) ∧
    -Real.log (2079 / 2500) ≤ (184403723 / 1000000000) := by
  have h := checkLog_sound (w := (421 / 4579)) (n := 12)
    (lo := (92201861 / 500000000)) (hi := (184403723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2079) = 1/(2079 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2534 : Bounds (-184403723 / 1000000000) (-92201861 / 500000000) (Real.log (2079 / 2500)) := by
  have h := reflection_log_2534_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2535_neg : (33677 / 200000000) ≤ -Real.log (2500000 / 2500421) ∧
    -Real.log (2500000 / 2500421) ≤ (84193 / 500000000) := by
  have h := checkLog_sound (w := (421 / 5000421)) (n := 12)
    (lo := (33677 / 200000000)) (hi := (84193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500421 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500421 / 2500000) = 1/(2500000 / 2500421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2535 : Bounds (33677 / 200000000) (84193 / 500000000) (Real.log (2500421 / 2500000)) := by
  have h := reflection_log_2535_neg
  have he : Real.log (2500421 / 2500000) = -Real.log (2500000 / 2500421) := by
    rw [show ((2500421 / 2500000) : ℝ) = ((2500000 / 2500421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2536_neg : (84207 / 500000000) ≤ -Real.log (2499579 / 2500000) ∧
    -Real.log (2499579 / 2500000) ≤ (33683 / 200000000) := by
  have h := checkLog_sound (w := (421 / 4999579)) (n := 12)
    (lo := (84207 / 500000000)) (hi := (33683 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499579) = 1/(2499579 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2536 : Bounds (-33683 / 200000000) (-84207 / 500000000) (Real.log (2499579 / 2500000)) := by
  have h := reflection_log_2536_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2537_neg : (81118129 / 1000000000) ≤ -Real.log (1000000 / 1084499) ∧
    -Real.log (1000000 / 1084499) ≤ (8111813 / 100000000) := by
  have h := checkLog_sound (w := (84499 / 2084499)) (n := 12)
    (lo := (81118129 / 1000000000)) (hi := (8111813 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084499 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084499 / 1000000) = 1/(1000000 / 1084499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2537 : Bounds (81118129 / 1000000000) (8111813 / 100000000) (Real.log (1084499 / 1000000)) := by
  have h := reflection_log_2537_neg
  have he : Real.log (1084499 / 1000000) = -Real.log (1000000 / 1084499) := by
    rw [show ((1084499 / 1000000) : ℝ) = ((1000000 / 1084499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2538_neg : (44141911 / 500000000) ≤ -Real.log (915501 / 1000000) ∧
    -Real.log (915501 / 1000000) ≤ (88283823 / 1000000000) := by
  have h := checkLog_sound (w := (84499 / 1915501)) (n := 12)
    (lo := (44141911 / 500000000)) (hi := (88283823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915501) = 1/(915501 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2538 : Bounds (-88283823 / 1000000000) (-44141911 / 500000000) (Real.log (915501 / 1000000)) := by
  have h := reflection_log_2538_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2539_neg : (16264009 / 200000000) ≤ -Real.log (500000 / 542359) ∧
    -Real.log (500000 / 542359) ≤ (40660023 / 500000000) := by
  have h := checkLog_sound (w := (42359 / 1042359)) (n := 12)
    (lo := (16264009 / 200000000)) (hi := (40660023 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((542359 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(542359 / 500000) = 1/(500000 / 542359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2539 : Bounds (16264009 / 200000000) (40660023 / 500000000) (Real.log (542359 / 500000)) := by
  have h := reflection_log_2539_neg
  have he : Real.log (542359 / 500000) = -Real.log (500000 / 542359) := by
    rw [show ((542359 / 500000) : ℝ) = ((500000 / 542359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2540_neg : (11065383 / 125000000) ≤ -Real.log (457641 / 500000) ∧
    -Real.log (457641 / 500000) ≤ (17704613 / 200000000) := by
  have h := checkLog_sound (w := (42359 / 957641)) (n := 12)
    (lo := (11065383 / 125000000)) (hi := (17704613 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 457641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 457641) = 1/(457641 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2540 : Bounds (-17704613 / 200000000) (-11065383 / 125000000) (Real.log (457641 / 500000)) := by
  have h := reflection_log_2540_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2541_neg : (7203019 / 1000000000) ≤ -Real.log (248205715119 / 250000000000) ∧
    -Real.log (248205715119 / 250000000000) ≤ (360151 / 50000000) := by
  have h := checkLog_sound (w := (1794284881 / 498205715119)) (n := 12)
    (lo := (7203019 / 1000000000)) (hi := (360151 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248205715119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248205715119) = 1/(248205715119 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2541 : Bounds (-360151 / 50000000) (-7203019 / 1000000000) (Real.log (248205715119 / 250000000000)) := by
  have h := reflection_log_2541_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2542_neg : (7165693 / 1000000000) ≤ -Real.log (992859918999 / 1000000000000) ∧
    -Real.log (992859918999 / 1000000000000) ≤ (3582847 / 500000000) := by
  have h := checkLog_sound (w := (7140081001 / 1992859918999)) (n := 12)
    (lo := (7165693 / 1000000000)) (hi := (3582847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992859918999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992859918999) = 1/(992859918999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2542 : Bounds (-3582847 / 500000000) (-7165693 / 1000000000) (Real.log (992859918999 / 1000000000000)) := by
  have h := reflection_log_2542_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2543_neg : (169401951 / 1000000000) ≤ -Real.log (500000000000 / 592298096889) ∧
    -Real.log (500000000000 / 592298096889) ≤ (5293811 / 31250000) := by
  have h := checkLog_sound (w := (92298096889 / 1092298096889)) (n := 12)
    (lo := (169401951 / 1000000000)) (hi := (5293811 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592298096889 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592298096889 / 500000000000) = 1/(500000000000 / 592298096889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2543 : Bounds (169401951 / 1000000000) (5293811 / 31250000) (Real.log (592298096889 / 500000000000)) := by
  have h := reflection_log_2543_neg
  have he : Real.log (592298096889 / 500000000000) = -Real.log (500000000000 / 592298096889) := by
    rw [show ((592298096889 / 500000000000) : ℝ) = ((500000000000 / 592298096889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2544_neg : (169843109 / 1000000000) ≤ -Real.log (500000000000 / 592559451623) ∧
    -Real.log (500000000000 / 592559451623) ≤ (16984311 / 100000000) := by
  have h := checkLog_sound (w := (92559451623 / 1092559451623)) (n := 12)
    (lo := (169843109 / 1000000000)) (hi := (16984311 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592559451623 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592559451623 / 500000000000) = 1/(500000000000 / 592559451623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2544 : Bounds (169843109 / 1000000000) (16984311 / 100000000) (Real.log (592559451623 / 500000000000)) := by
  have h := reflection_log_2544_neg
  have he : Real.log (592559451623 / 500000000000) = -Real.log (500000000000 / 592559451623) := by
    rw [show ((592559451623 / 500000000000) : ℝ) = ((500000000000 / 592559451623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2545_neg : (16991659 / 50000000) ≤ -Real.log (500000000000 / 702356618973) ∧
    -Real.log (500000000000 / 702356618973) ≤ (339833181 / 1000000000) := by
  have h := checkLog_sound (w := (202356618973 / 1202356618973)) (n := 12)
    (lo := (16991659 / 50000000)) (hi := (339833181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((702356618973 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(702356618973 / 500000000000) = 1/(500000000000 / 702356618973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2545 : Bounds (16991659 / 50000000) (339833181 / 1000000000) (Real.log (702356618973 / 500000000000)) := by
  have h := reflection_log_2545_neg
  have he : Real.log (702356618973 / 500000000000) = -Real.log (500000000000 / 702356618973) := by
    rw [show ((702356618973 / 500000000000) : ℝ) = ((500000000000 / 702356618973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2546_neg : (170019507 / 500000000) ≤ -Real.log (250000000000 / 351250601251) ∧
    -Real.log (250000000000 / 351250601251) ≤ (68007803 / 200000000) := by
  have h := checkLog_sound (w := (101250601251 / 601250601251)) (n := 12)
    (lo := (170019507 / 500000000)) (hi := (68007803 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351250601251 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351250601251 / 250000000000) = 1/(250000000000 / 351250601251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2546 : Bounds (170019507 / 500000000) (68007803 / 200000000) (Real.log (351250601251 / 250000000000)) := by
  have h := reflection_log_2546_neg
  have he : Real.log (351250601251 / 250000000000) = -Real.log (250000000000 / 351250601251) := by
    rw [show ((351250601251 / 250000000000) : ℝ) = ((250000000000 / 351250601251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2547_neg : (77860437 / 500000000) ≤ -Real.log (2000 / 2337) ∧
    -Real.log (2000 / 2337) ≤ (1245767 / 8000000) := by
  have h := checkLog_sound (w := (337 / 4337)) (n := 12)
    (lo := (77860437 / 500000000)) (hi := (1245767 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2337 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2337 / 2000) = 1/(2000 / 2337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2547 : Bounds (77860437 / 500000000) (1245767 / 8000000) (Real.log (2337 / 2000)) := by
  have h := reflection_log_2547_neg
  have he : Real.log (2337 / 2000) = -Real.log (2000 / 2337) := by
    rw [show ((2337 / 2000) : ℝ) = ((2000 / 2337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2548_neg : (9226199 / 50000000) ≤ -Real.log (1663 / 2000) ∧
    -Real.log (1663 / 2000) ≤ (184523981 / 1000000000) := by
  have h := checkLog_sound (w := (337 / 3663)) (n := 12)
    (lo := (9226199 / 50000000)) (hi := (184523981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1663) = 1/(1663 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2548 : Bounds (-184523981 / 1000000000) (-9226199 / 50000000) (Real.log (1663 / 2000)) := by
  have h := reflection_log_2548_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2549_neg : (33697 / 200000000) ≤ -Real.log (2000000 / 2000337) ∧
    -Real.log (2000000 / 2000337) ≤ (84243 / 500000000) := by
  have h := checkLog_sound (w := (337 / 4000337)) (n := 12)
    (lo := (33697 / 200000000)) (hi := (84243 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000337 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000337 / 2000000) = 1/(2000000 / 2000337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2549 : Bounds (33697 / 200000000) (84243 / 500000000) (Real.log (2000337 / 2000000)) := by
  have h := reflection_log_2549_neg
  have he : Real.log (2000337 / 2000000) = -Real.log (2000000 / 2000337) := by
    rw [show ((2000337 / 2000000) : ℝ) = ((2000000 / 2000337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2550_neg : (84257 / 500000000) ≤ -Real.log (1999663 / 2000000) ∧
    -Real.log (1999663 / 2000000) ≤ (33703 / 200000000) := by
  have h := checkLog_sound (w := (337 / 3999663)) (n := 12)
    (lo := (84257 / 500000000)) (hi := (33703 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999663) = 1/(1999663 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2550 : Bounds (-33703 / 200000000) (-84257 / 500000000) (Real.log (1999663 / 2000000)) := by
  have h := reflection_log_2550_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2551_neg : (40582577 / 500000000) ≤ -Real.log (20000 / 21691) ∧
    -Real.log (20000 / 21691) ≤ (16233031 / 200000000) := by
  have h := checkLog_sound (w := (1691 / 41691)) (n := 12)
    (lo := (40582577 / 500000000)) (hi := (16233031 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21691 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21691 / 20000) = 1/(20000 / 21691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2551 : Bounds (40582577 / 500000000) (16233031 / 200000000) (Real.log (21691 / 20000)) := by
  have h := reflection_log_2551_neg
  have he : Real.log (21691 / 20000) = -Real.log (20000 / 21691) := by
    rw [show ((21691 / 20000) : ℝ) = ((20000 / 21691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2552_neg : (88339531 / 1000000000) ≤ -Real.log (18309 / 20000) ∧
    -Real.log (18309 / 20000) ≤ (22084883 / 250000000) := by
  have h := checkLog_sound (w := (1691 / 38309)) (n := 12)
    (lo := (88339531 / 1000000000)) (hi := (22084883 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 18309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 18309) = 1/(18309 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2552 : Bounds (-22084883 / 250000000) (-88339531 / 1000000000) (Real.log (18309 / 20000)) := by
  have h := reflection_log_2552_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2553_neg : (81367061 / 1000000000) ≤ -Real.log (1000000 / 1084769) ∧
    -Real.log (1000000 / 1084769) ≤ (40683531 / 500000000) := by
  have h := checkLog_sound (w := (84769 / 2084769)) (n := 12)
    (lo := (81367061 / 1000000000)) (hi := (40683531 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084769 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1084769 / 1000000) = 1/(1000000 / 1084769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2553 : Bounds (81367061 / 1000000000) (40683531 / 500000000) (Real.log (1084769 / 1000000)) := by
  have h := reflection_log_2553_neg
  have he : Real.log (1084769 / 1000000) = -Real.log (1000000 / 1084769) := by
    rw [show ((1084769 / 1000000) : ℝ) = ((1000000 / 1084769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2554_neg : (44289393 / 500000000) ≤ -Real.log (915231 / 1000000) ∧
    -Real.log (915231 / 1000000) ≤ (88578787 / 1000000000) := by
  have h := checkLog_sound (w := (84769 / 1915231)) (n := 12)
    (lo := (44289393 / 500000000)) (hi := (88578787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 915231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 915231) = 1/(915231 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2554 : Bounds (-88578787 / 1000000000) (-44289393 / 500000000) (Real.log (915231 / 1000000)) := by
  have h := reflection_log_2554_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2555_neg : (288469 / 40000000) ≤ -Real.log (992814216639 / 1000000000000) ∧
    -Real.log (992814216639 / 1000000000000) ≤ (3605863 / 500000000) := by
  have h := checkLog_sound (w := (7185783361 / 1992814216639)) (n := 12)
    (lo := (288469 / 40000000)) (hi := (3605863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992814216639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992814216639) = 1/(992814216639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2555 : Bounds (-3605863 / 500000000) (-288469 / 40000000) (Real.log (992814216639 / 1000000000000)) := by
  have h := reflection_log_2555_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2556_neg : (896797 / 125000000) ≤ -Real.log (397140519 / 400000000) ∧
    -Real.log (397140519 / 400000000) ≤ (7174377 / 1000000000) := by
  have h := checkLog_sound (w := (2859481 / 797140519)) (n := 12)
    (lo := (896797 / 125000000)) (hi := (7174377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 397140519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 397140519) = 1/(397140519 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2556 : Bounds (-7174377 / 1000000000) (-896797 / 125000000) (Real.log (397140519 / 400000000)) := by
  have h := reflection_log_2556_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2557_neg : (33900937 / 200000000) ≤ -Real.log (10000000000 / 11847178983) ∧
    -Real.log (10000000000 / 11847178983) ≤ (84752343 / 500000000) := by
  have h := checkLog_sound (w := (1847178983 / 21847178983)) (n := 12)
    (lo := (33900937 / 200000000)) (hi := (84752343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11847178983 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11847178983 / 10000000000) = 1/(10000000000 / 11847178983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2557 : Bounds (33900937 / 200000000) (84752343 / 500000000) (Real.log (11847178983 / 10000000000)) := by
  have h := reflection_log_2557_neg
  have he : Real.log (11847178983 / 10000000000) = -Real.log (10000000000 / 11847178983) := by
    rw [show ((11847178983 / 10000000000) : ℝ) = ((10000000000 / 11847178983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2558_neg : (169945847 / 1000000000) ≤ -Real.log (500000000000 / 592620333009) ∧
    -Real.log (500000000000 / 592620333009) ≤ (21243231 / 125000000) := by
  have h := checkLog_sound (w := (92620333009 / 1092620333009)) (n := 12)
    (lo := (169945847 / 1000000000)) (hi := (21243231 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592620333009 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592620333009 / 500000000000) = 1/(500000000000 / 592620333009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2558 : Bounds (169945847 / 1000000000) (21243231 / 125000000) (Real.log (592620333009 / 500000000000)) := by
  have h := reflection_log_2558_neg
  have he : Real.log (592620333009 / 500000000000) = -Real.log (500000000000 / 592620333009) := by
    rw [show ((592620333009 / 500000000000) : ℝ) = ((500000000000 / 592620333009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2559_neg : (170019507 / 500000000) ≤ -Real.log (500000000000 / 702501202501) ∧
    -Real.log (500000000000 / 702501202501) ≤ (68007803 / 200000000) := by
  have h := checkLog_sound (w := (202501202501 / 1202501202501)) (n := 12)
    (lo := (170019507 / 500000000)) (hi := (68007803 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((702501202501 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(702501202501 / 500000000000) = 1/(500000000000 / 702501202501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2559 : Bounds (170019507 / 500000000) (68007803 / 200000000) (Real.log (702501202501 / 500000000000)) := by
  have h := reflection_log_2559_neg
  have he : Real.log (702501202501 / 500000000000) = -Real.log (500000000000 / 702501202501) := by
    rw [show ((702501202501 / 500000000000) : ℝ) = ((500000000000 / 702501202501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
