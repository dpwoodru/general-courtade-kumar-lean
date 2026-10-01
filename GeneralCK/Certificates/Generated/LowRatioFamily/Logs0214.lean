import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13696_neg : (893078217 / 1000000000) ≤ -Real.log (250000000000 / 610659264997) ∧
    -Real.log (250000000000 / 610659264997) ≤ (893078219 / 1000000000) := by
  have h := checkLog_sound (w := (110659264997 / 1110659264997)) (n := 12)
    (lo := (199931037 / 1000000000)) (hi := (99965519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((610659264997 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(610659264997 / 500000000000) = 1/(250000000000 / 610659264997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13696 : Bounds (893078217 / 1000000000) (893078219 / 1000000000) (Real.log (610659264997 / 250000000000)) := by
  have h := reflection_log_13696_neg
  have he : Real.log (610659264997 / 250000000000) = -Real.log (250000000000 / 610659264997) := by
    rw [show ((610659264997 / 250000000000) : ℝ) = ((250000000000 / 610659264997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13697_neg : (1914286959 / 1000000000) ≤ -Real.log (500000000000 / 3391050583657) ∧
    -Real.log (500000000000 / 3391050583657) ≤ (957143481 / 500000000) := by
  have h := checkLog_sound (w := (1391050583657 / 5391050583657)) (n := 12)
    (lo := (527992599 / 1000000000)) (hi := (2639963 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3391050583657 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3391050583657 / 2000000000000) = 1/(500000000000 / 3391050583657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13697 : Bounds (1914286959 / 1000000000) (957143481 / 500000000) (Real.log (3391050583657 / 500000000000)) := by
  have h := reflection_log_13697_neg
  have he : Real.log (3391050583657 / 500000000000) = -Real.log (500000000000 / 3391050583657) := by
    rw [show ((3391050583657 / 500000000000) : ℝ) = ((500000000000 / 3391050583657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13698_neg : (481937117 / 250000000) ≤ -Real.log (15625000000 / 107406496063) ∧
    -Real.log (15625000000 / 107406496063) ≤ (1927748471 / 1000000000) := by
  have h := checkLog_sound (w := (44906496063 / 169906496063)) (n := 12)
    (lo := (135363527 / 250000000)) (hi := (541454109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((107406496063 / 62500000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(107406496063 / 62500000000) = 1/(15625000000 / 107406496063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13698 : Bounds (481937117 / 250000000) (1927748471 / 1000000000) (Real.log (107406496063 / 15625000000)) := by
  have h := reflection_log_13698_neg
  have he : Real.log (107406496063 / 15625000000) = -Real.log (15625000000 / 107406496063) := by
    rw [show ((107406496063 / 15625000000) : ℝ) = ((15625000000 / 107406496063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13699_neg : (139761049 / 250000000) ≤ -Real.log (1000 / 1749) ∧
    -Real.log (1000 / 1749) ≤ (559044197 / 1000000000) := by
  have h := checkLog_sound (w := (749 / 2749)) (n := 12)
    (lo := (139761049 / 250000000)) (hi := (559044197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1749 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1749 / 1000) = 1/(1000 / 1749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13699 : Bounds (139761049 / 250000000) (559044197 / 1000000000) (Real.log (1749 / 1000)) := by
  have h := reflection_log_13699_neg
  have he : Real.log (1749 / 1000) = -Real.log (1000 / 1749) := by
    rw [show ((1749 / 1000) : ℝ) = ((1000 / 1749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13700_neg : (1382302339 / 1000000000) ≤ -Real.log (251 / 1000) ∧
    -Real.log (251 / 1000) ≤ (1382302341 / 1000000000) := by
  have h := checkLog_sound (w := (249 / 751)) (n := 12)
    (lo := (689155159 / 1000000000)) (hi := (17228879 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 251) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 251) = 1/(251 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13700 : Bounds (-1382302341 / 1000000000) (-1382302339 / 1000000000) (Real.log (251 / 1000)) := by
  have h := reflection_log_13700_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13701_neg : (748719 / 1000000000) ≤ -Real.log (1000000 / 1000749) ∧
    -Real.log (1000000 / 1000749) ≤ (9359 / 12500000) := by
  have h := checkLog_sound (w := (749 / 2000749)) (n := 12)
    (lo := (748719 / 1000000000)) (hi := (9359 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000749 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000749 / 1000000) = 1/(1000000 / 1000749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13701 : Bounds (748719 / 1000000000) (9359 / 12500000) (Real.log (1000749 / 1000000)) := by
  have h := reflection_log_13701_neg
  have he : Real.log (1000749 / 1000000) = -Real.log (1000000 / 1000749) := by
    rw [show ((1000749 / 1000000) : ℝ) = ((1000000 / 1000749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13702_neg : (4683 / 6250000) ≤ -Real.log (999251 / 1000000) ∧
    -Real.log (999251 / 1000000) ≤ (749281 / 1000000000) := by
  have h := checkLog_sound (w := (749 / 1999251)) (n := 12)
    (lo := (4683 / 6250000)) (hi := (749281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999251) = 1/(999251 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13702 : Bounds (-749281 / 1000000000) (-4683 / 6250000) (Real.log (999251 / 1000000)) := by
  have h := reflection_log_13702_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13703_neg : (13981461 / 40000000) ≤ -Real.log (100000 / 141841) ∧
    -Real.log (100000 / 141841) ≤ (174768263 / 500000000) := by
  have h := checkLog_sound (w := (41841 / 241841)) (n := 12)
    (lo := (13981461 / 40000000)) (hi := (174768263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141841 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(141841 / 100000) = 1/(100000 / 141841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13703 : Bounds (13981461 / 40000000) (174768263 / 500000000) (Real.log (141841 / 100000)) := by
  have h := reflection_log_13703_neg
  have he : Real.log (141841 / 100000) = -Real.log (100000 / 141841) := by
    rw [show ((141841 / 100000) : ℝ) = ((100000 / 141841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13704_neg : (270994773 / 500000000) ≤ -Real.log (58159 / 100000) ∧
    -Real.log (58159 / 100000) ≤ (541989547 / 1000000000) := by
  have h := checkLog_sound (w := (41841 / 158159)) (n := 12)
    (lo := (270994773 / 500000000)) (hi := (541989547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 58159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 58159) = 1/(58159 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13704 : Bounds (-541989547 / 1000000000) (-270994773 / 500000000) (Real.log (58159 / 100000)) := by
  have h := reflection_log_13704_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13705_neg : (21968893 / 62500000) ≤ -Real.log (1000000 / 1421201) ∧
    -Real.log (1000000 / 1421201) ≤ (351502289 / 1000000000) := by
  have h := checkLog_sound (w := (421201 / 2421201)) (n := 12)
    (lo := (21968893 / 62500000)) (hi := (351502289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1421201 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1421201 / 1000000) = 1/(1000000 / 1421201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13705 : Bounds (21968893 / 62500000) (351502289 / 1000000000) (Real.log (1421201 / 1000000)) := by
  have h := reflection_log_13705_neg
  have he : Real.log (1421201 / 1000000) = -Real.log (1000000 / 1421201) := by
    rw [show ((1421201 / 1000000) : ℝ) = ((1000000 / 1421201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13706_neg : (546800011 / 1000000000) ≤ -Real.log (578799 / 1000000) ∧
    -Real.log (578799 / 1000000) ≤ (136700003 / 250000000) := by
  have h := checkLog_sound (w := (421201 / 1578799)) (n := 12)
    (lo := (546800011 / 1000000000)) (hi := (136700003 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 578799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 578799) = 1/(578799 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13706 : Bounds (-136700003 / 250000000) (-546800011 / 1000000000) (Real.log (578799 / 1000000)) := by
  have h := reflection_log_13706_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13707_neg : (195297723 / 1000000000) ≤ -Real.log (822589717599 / 1000000000000) ∧
    -Real.log (822589717599 / 1000000000000) ≤ (48824431 / 250000000) := by
  have h := checkLog_sound (w := (177410282401 / 1822589717599)) (n := 12)
    (lo := (195297723 / 1000000000)) (hi := (48824431 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 822589717599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 822589717599) = 1/(822589717599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13707 : Bounds (-48824431 / 250000000) (-195297723 / 1000000000) (Real.log (822589717599 / 1000000000000)) := by
  have h := reflection_log_13707_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13708_neg : (9622651 / 50000000) ≤ -Real.log (8249330719 / 10000000000) ∧
    -Real.log (8249330719 / 10000000000) ≤ (192453021 / 1000000000) := by
  have h := checkLog_sound (w := (1750669281 / 18249330719)) (n := 12)
    (lo := (9622651 / 50000000)) (hi := (192453021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 8249330719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 8249330719) = 1/(8249330719 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13708 : Bounds (-192453021 / 1000000000) (-9622651 / 50000000) (Real.log (8249330719 / 10000000000)) := by
  have h := reflection_log_13708_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13709_neg : (111440759 / 125000000) ≤ -Real.log (125000000000 / 304856084183) ∧
    -Real.log (125000000000 / 304856084183) ≤ (445763037 / 500000000) := by
  have h := checkLog_sound (w := (54856084183 / 554856084183)) (n := 12)
    (lo := (49594723 / 250000000)) (hi := (198378893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((304856084183 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(304856084183 / 250000000000) = 1/(125000000000 / 304856084183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13709 : Bounds (111440759 / 125000000) (445763037 / 500000000) (Real.log (304856084183 / 125000000000)) := by
  have h := reflection_log_13709_neg
  have he : Real.log (304856084183 / 125000000000) = -Real.log (125000000000 / 304856084183) := by
    rw [show ((304856084183 / 125000000000) : ℝ) = ((125000000000 / 304856084183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13710_neg : (8983023 / 10000000) ≤ -Real.log (100000000000 / 245543098727) ∧
    -Real.log (100000000000 / 245543098727) ≤ (449151151 / 500000000) := by
  have h := checkLog_sound (w := (45543098727 / 445543098727)) (n := 12)
    (lo := (2564439 / 12500000)) (hi := (205155121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((245543098727 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(245543098727 / 200000000000) = 1/(100000000000 / 245543098727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13710 : Bounds (8983023 / 10000000) (449151151 / 500000000) (Real.log (245543098727 / 100000000000)) := by
  have h := reflection_log_13710_neg
  have he : Real.log (245543098727 / 100000000000) = -Real.log (100000000000 / 245543098727) := by
    rw [show ((245543098727 / 100000000000) : ℝ) = ((100000000000 / 245543098727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13711_neg : (481937117 / 250000000) ≤ -Real.log (100000000000 / 687401574803) ∧
    -Real.log (100000000000 / 687401574803) ≤ (1927748471 / 1000000000) := by
  have h := checkLog_sound (w := (287401574803 / 1087401574803)) (n := 12)
    (lo := (135363527 / 250000000)) (hi := (541454109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((687401574803 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(687401574803 / 400000000000) = 1/(100000000000 / 687401574803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13711 : Bounds (481937117 / 250000000) (1927748471 / 1000000000) (Real.log (687401574803 / 100000000000)) := by
  have h := reflection_log_13711_neg
  have he : Real.log (687401574803 / 100000000000) = -Real.log (100000000000 / 687401574803) := by
    rw [show ((687401574803 / 100000000000) : ℝ) = ((100000000000 / 687401574803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13712_neg : (970673267 / 500000000) ≤ -Real.log (25000000000 / 174203187251) ∧
    -Real.log (25000000000 / 174203187251) ≤ (1941346537 / 1000000000) := by
  have h := checkLog_sound (w := (74203187251 / 274203187251)) (n := 12)
    (lo := (277526087 / 500000000)) (hi := (22202087 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((174203187251 / 100000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(174203187251 / 100000000000) = 1/(25000000000 / 174203187251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13712 : Bounds (970673267 / 500000000) (1941346537 / 1000000000) (Real.log (174203187251 / 25000000000)) := by
  have h := reflection_log_13712_neg
  have he : Real.log (174203187251 / 25000000000) = -Real.log (25000000000 / 174203187251) := by
    rw [show ((174203187251 / 25000000000) : ℝ) = ((25000000000 / 174203187251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13713_neg : (70094749 / 125000000) ≤ -Real.log (125 / 219) ∧
    -Real.log (125 / 219) ≤ (560757993 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 172)) (n := 12)
    (lo := (70094749 / 125000000)) (hi := (560757993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((219 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(219 / 125) = 1/(125 / 219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13713 : Bounds (70094749 / 125000000) (560757993 / 1000000000) (Real.log (219 / 125)) := by
  have h := reflection_log_13713_neg
  have he : Real.log (219 / 125) = -Real.log (125 / 219) := by
    rw [show ((219 / 125) : ℝ) = ((125 / 219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13714_neg : (1394326531 / 1000000000) ≤ -Real.log (31 / 125) ∧
    -Real.log (31 / 125) ≤ (697163267 / 500000000) := by
  have h := checkLog_sound (w := (1 / 249)) (n := 12)
    (lo := (8032171 / 1000000000)) (hi := (2008043 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 124) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 124) = 1/(31 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13714 : Bounds (-697163267 / 500000000) (-1394326531 / 1000000000) (Real.log (31 / 125)) := by
  have h := reflection_log_13714_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13715_neg : (751717 / 1000000000) ≤ -Real.log (62500 / 62547) ∧
    -Real.log (62500 / 62547) ≤ (375859 / 500000000) := by
  have h := checkLog_sound (w := (47 / 125047)) (n := 12)
    (lo := (751717 / 1000000000)) (hi := (375859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62547 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62547 / 62500) = 1/(62500 / 62547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13715 : Bounds (751717 / 1000000000) (375859 / 500000000) (Real.log (62547 / 62500)) := by
  have h := reflection_log_13715_neg
  have he : Real.log (62547 / 62500) = -Real.log (62500 / 62547) := by
    rw [show ((62547 / 62500) : ℝ) = ((62500 / 62547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13716_neg : (376141 / 500000000) ≤ -Real.log (62453 / 62500) ∧
    -Real.log (62453 / 62500) ≤ (752283 / 1000000000) := by
  have h := checkLog_sound (w := (47 / 124953)) (n := 12)
    (lo := (376141 / 500000000)) (hi := (752283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62453) = 1/(62453 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13716 : Bounds (-752283 / 1000000000) (-376141 / 500000000) (Real.log (62453 / 62500)) := by
  have h := reflection_log_13716_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13717_neg : (43881307 / 125000000) ≤ -Real.log (1000000 / 1420559) ∧
    -Real.log (1000000 / 1420559) ≤ (351050457 / 1000000000) := by
  have h := checkLog_sound (w := (420559 / 2420559)) (n := 12)
    (lo := (43881307 / 125000000)) (hi := (351050457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1420559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1420559 / 1000000) = 1/(1000000 / 1420559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13717 : Bounds (43881307 / 125000000) (351050457 / 1000000000) (Real.log (1420559 / 1000000)) := by
  have h := reflection_log_13717_neg
  have he : Real.log (1420559 / 1000000) = -Real.log (1000000 / 1420559) := by
    rw [show ((1420559 / 1000000) : ℝ) = ((1000000 / 1420559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13718_neg : (545691433 / 1000000000) ≤ -Real.log (579441 / 1000000) ∧
    -Real.log (579441 / 1000000) ≤ (272845717 / 500000000) := by
  have h := checkLog_sound (w := (420559 / 1579441)) (n := 12)
    (lo := (545691433 / 1000000000)) (hi := (272845717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 579441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 579441) = 1/(579441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13718 : Bounds (-272845717 / 500000000) (-545691433 / 1000000000) (Real.log (579441 / 1000000)) := by
  have h := reflection_log_13718_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13719_neg : (353020273 / 1000000000) ≤ -Real.log (3125 / 4448) ∧
    -Real.log (3125 / 4448) ≤ (176510137 / 500000000) := by
  have h := checkLog_sound (w := (1323 / 7573)) (n := 12)
    (lo := (353020273 / 1000000000)) (hi := (176510137 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4448 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4448 / 3125) = 1/(3125 / 4448) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13719 : Bounds (353020273 / 1000000000) (176510137 / 500000000) (Real.log (4448 / 3125)) := by
  have h := reflection_log_13719_neg
  have he : Real.log (4448 / 3125) = -Real.log (3125 / 4448) := by
    rw [show ((4448 / 3125) : ℝ) = ((3125 / 4448) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13720_neg : (137634281 / 250000000) ≤ -Real.log (1802 / 3125) ∧
    -Real.log (1802 / 3125) ≤ (4404297 / 8000000) := by
  have h := checkLog_sound (w := (1323 / 4927)) (n := 12)
    (lo := (137634281 / 250000000)) (hi := (4404297 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1802) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3125 / 1802) = 1/(1802 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13720 : Bounds (-4404297 / 8000000) (-137634281 / 250000000) (Real.log (1802 / 3125)) := by
  have h := reflection_log_13720_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13721_neg : (3950337 / 20000000) ≤ -Real.log (8015296 / 9765625) ∧
    -Real.log (8015296 / 9765625) ≤ (197516851 / 1000000000) := by
  have h := checkLog_sound (w := (1750329 / 17780921)) (n := 12)
    (lo := (3950337 / 20000000)) (hi := (197516851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9765625 / 8015296) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9765625 / 8015296) = 1/(8015296 / 9765625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13721 : Bounds (-197516851 / 1000000000) (-3950337 / 20000000) (Real.log (8015296 / 9765625)) := by
  have h := reflection_log_13721_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13722_neg : (194640977 / 1000000000) ≤ -Real.log (823130127519 / 1000000000000) ∧
    -Real.log (823130127519 / 1000000000000) ≤ (97320489 / 500000000) := by
  have h := checkLog_sound (w := (176869872481 / 1823130127519)) (n := 12)
    (lo := (194640977 / 1000000000)) (hi := (97320489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 823130127519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 823130127519) = 1/(823130127519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13722 : Bounds (-97320489 / 500000000) (-194640977 / 1000000000) (Real.log (823130127519 / 1000000000000)) := by
  have h := reflection_log_13722_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13723_neg : (1751449 / 1953125) ≤ -Real.log (500000000000 / 1225801246373) ∧
    -Real.log (500000000000 / 1225801246373) ≤ (89674189 / 100000000) := by
  have h := checkLog_sound (w := (225801246373 / 2225801246373)) (n := 12)
    (lo := (50898677 / 250000000)) (hi := (203594709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1225801246373 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1225801246373 / 1000000000000) = 1/(500000000000 / 1225801246373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13723 : Bounds (1751449 / 1953125) (89674189 / 100000000) (Real.log (1225801246373 / 500000000000)) := by
  have h := reflection_log_13723_neg
  have he : Real.log (1225801246373 / 500000000000) = -Real.log (500000000000 / 1225801246373) := by
    rw [show ((1225801246373 / 500000000000) : ℝ) = ((500000000000 / 1225801246373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13724_neg : (903557397 / 1000000000) ≤ -Real.log (250000000000 / 617092119867) ∧
    -Real.log (250000000000 / 617092119867) ≤ (903557399 / 1000000000) := by
  have h := checkLog_sound (w := (117092119867 / 1117092119867)) (n := 12)
    (lo := (210410217 / 1000000000)) (hi := (105205109 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((617092119867 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(617092119867 / 500000000000) = 1/(250000000000 / 617092119867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13724 : Bounds (903557397 / 1000000000) (903557399 / 1000000000) (Real.log (617092119867 / 250000000000)) := by
  have h := reflection_log_13724_neg
  have he : Real.log (617092119867 / 250000000000) = -Real.log (250000000000 / 617092119867) := by
    rw [show ((617092119867 / 250000000000) : ℝ) = ((250000000000 / 617092119867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13725_neg : (970673267 / 500000000) ≤ -Real.log (500000000000 / 3484063745019) ∧
    -Real.log (500000000000 / 3484063745019) ≤ (1941346537 / 1000000000) := by
  have h := checkLog_sound (w := (1484063745019 / 5484063745019)) (n := 12)
    (lo := (277526087 / 500000000)) (hi := (22202087 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3484063745019 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3484063745019 / 2000000000000) = 1/(500000000000 / 3484063745019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13725 : Bounds (970673267 / 500000000) (1941346537 / 1000000000) (Real.log (3484063745019 / 500000000000)) := by
  have h := reflection_log_13725_neg
  have he : Real.log (3484063745019 / 500000000000) = -Real.log (500000000000 / 3484063745019) := by
    rw [show ((3484063745019 / 500000000000) : ℝ) = ((500000000000 / 3484063745019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13726_neg : (488771131 / 250000000) ≤ -Real.log (500000000000 / 3532258064517) ∧
    -Real.log (500000000000 / 3532258064517) ≤ (1955084527 / 1000000000) := by
  have h := checkLog_sound (w := (1532258064517 / 5532258064517)) (n := 12)
    (lo := (142197541 / 250000000)) (hi := (113758033 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3532258064517 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3532258064517 / 2000000000000) = 1/(500000000000 / 3532258064517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13726 : Bounds (488771131 / 250000000) (1955084527 / 1000000000) (Real.log (3532258064517 / 500000000000)) := by
  have h := reflection_log_13726_neg
  have he : Real.log (3532258064517 / 500000000000) = -Real.log (500000000000 / 3532258064517) := by
    rw [show ((3532258064517 / 500000000000) : ℝ) = ((500000000000 / 3532258064517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13727_neg : (70308607 / 125000000) ≤ -Real.log (200 / 351) ∧
    -Real.log (200 / 351) ≤ (562468857 / 1000000000) := by
  have h := checkLog_sound (w := (151 / 551)) (n := 12)
    (lo := (70308607 / 125000000)) (hi := (562468857 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351 / 200) = 1/(200 / 351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13727 : Bounds (70308607 / 125000000) (562468857 / 1000000000) (Real.log (351 / 200)) := by
  have h := reflection_log_13727_neg
  have he : Real.log (351 / 200) = -Real.log (200 / 351) := by
    rw [show ((351 / 200) : ℝ) = ((200 / 351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13728_neg : (1406497067 / 1000000000) ≤ -Real.log (49 / 200) ∧
    -Real.log (49 / 200) ≤ (140649707 / 100000000) := by
  have h := checkLog_sound (w := (1 / 99)) (n := 12)
    (lo := (20202707 / 1000000000)) (hi := (5050677 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 49) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50 / 49) = 1/(49 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13728 : Bounds (-140649707 / 100000000) (-1406497067 / 1000000000) (Real.log (49 / 200)) := by
  have h := reflection_log_13728_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13729_neg : (150943 / 200000000) ≤ -Real.log (200000 / 200151) ∧
    -Real.log (200000 / 200151) ≤ (188679 / 250000000) := by
  have h := checkLog_sound (w := (151 / 400151)) (n := 12)
    (lo := (150943 / 200000000)) (hi := (188679 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200151 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200151 / 200000) = 1/(200000 / 200151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13729 : Bounds (150943 / 200000000) (188679 / 250000000) (Real.log (200151 / 200000)) := by
  have h := reflection_log_13729_neg
  have he : Real.log (200151 / 200000) = -Real.log (200000 / 200151) := by
    rw [show ((200151 / 200000) : ℝ) = ((200000 / 200151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13730_neg : (151057 / 200000000) ≤ -Real.log (199849 / 200000) ∧
    -Real.log (199849 / 200000) ≤ (377643 / 500000000) := by
  have h := checkLog_sound (w := (151 / 399849)) (n := 12)
    (lo := (151057 / 200000000)) (hi := (377643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199849) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199849) = 1/(199849 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13730 : Bounds (-377643 / 500000000) (-151057 / 200000000) (Real.log (199849 / 200000)) := by
  have h := reflection_log_13730_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13731_neg : (352568423 / 1000000000) ≤ -Real.log (1000000 / 1422717) ∧
    -Real.log (1000000 / 1422717) ≤ (44071053 / 125000000) := by
  have h := checkLog_sound (w := (422717 / 2422717)) (n := 12)
    (lo := (352568423 / 1000000000)) (hi := (44071053 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1422717 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1422717 / 1000000) = 1/(1000000 / 1422717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13731 : Bounds (352568423 / 1000000000) (44071053 / 125000000) (Real.log (1422717 / 1000000)) := by
  have h := reflection_log_13731_neg
  have he : Real.log (1422717 / 1000000) = -Real.log (1000000 / 1422717) := by
    rw [show ((1422717 / 1000000) : ℝ) = ((1000000 / 1422717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13732_neg : (68677833 / 125000000) ≤ -Real.log (577283 / 1000000) ∧
    -Real.log (577283 / 1000000) ≤ (109884533 / 200000000) := by
  have h := checkLog_sound (w := (422717 / 1577283)) (n := 12)
    (lo := (68677833 / 125000000)) (hi := (109884533 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 577283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 577283) = 1/(577283 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13732 : Bounds (-109884533 / 200000000) (-68677833 / 125000000) (Real.log (577283 / 1000000)) := by
  have h := reflection_log_13732_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13733_neg : (354541569 / 1000000000) ≤ -Real.log (1000000 / 1425527) ∧
    -Real.log (1000000 / 1425527) ≤ (35454157 / 100000000) := by
  have h := checkLog_sound (w := (425527 / 2425527)) (n := 12)
    (lo := (354541569 / 1000000000)) (hi := (35454157 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1425527 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1425527 / 1000000) = 1/(1000000 / 1425527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13733 : Bounds (354541569 / 1000000000) (35454157 / 100000000) (Real.log (1425527 / 1000000)) := by
  have h := reflection_log_13733_neg
  have he : Real.log (1425527 / 1000000) = -Real.log (1000000 / 1425527) := by
    rw [show ((1425527 / 1000000) : ℝ) = ((1000000 / 1425527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13734_neg : (27715109 / 50000000) ≤ -Real.log (574473 / 1000000) ∧
    -Real.log (574473 / 1000000) ≤ (554302181 / 1000000000) := by
  have h := checkLog_sound (w := (425527 / 1574473)) (n := 12)
    (lo := (27715109 / 50000000)) (hi := (554302181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 574473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 574473) = 1/(574473 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13734 : Bounds (-554302181 / 1000000000) (-27715109 / 50000000) (Real.log (574473 / 1000000)) := by
  have h := reflection_log_13734_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13735_neg : (19976061 / 100000000) ≤ -Real.log (818926772271 / 1000000000000) ∧
    -Real.log (818926772271 / 1000000000000) ≤ (199760611 / 1000000000) := by
  have h := checkLog_sound (w := (181073227729 / 1818926772271)) (n := 12)
    (lo := (19976061 / 100000000)) (hi := (199760611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 818926772271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 818926772271) = 1/(818926772271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13735 : Bounds (-199760611 / 1000000000) (-19976061 / 100000000) (Real.log (818926772271 / 1000000000000)) := by
  have h := reflection_log_13735_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13736_neg : (196854241 / 1000000000) ≤ -Real.log (821310337911 / 1000000000000) ∧
    -Real.log (821310337911 / 1000000000000) ≤ (98427121 / 500000000) := by
  have h := checkLog_sound (w := (178689662089 / 1821310337911)) (n := 12)
    (lo := (196854241 / 1000000000)) (hi := (98427121 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 821310337911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 821310337911) = 1/(821310337911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13736 : Bounds (-98427121 / 500000000) (-196854241 / 1000000000) (Real.log (821310337911 / 1000000000000)) := by
  have h := reflection_log_13736_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13737_neg : (901991087 / 1000000000) ≤ -Real.log (500000000000 / 1232252638653) ∧
    -Real.log (500000000000 / 1232252638653) ≤ (901991089 / 1000000000) := by
  have h := checkLog_sound (w := (232252638653 / 2232252638653)) (n := 12)
    (lo := (208843907 / 1000000000)) (hi := (52210977 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1232252638653 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1232252638653 / 1000000000000) = 1/(500000000000 / 1232252638653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13737 : Bounds (901991087 / 1000000000) (901991089 / 1000000000) (Real.log (1232252638653 / 500000000000)) := by
  have h := reflection_log_13737_neg
  have he : Real.log (1232252638653 / 500000000000) = -Real.log (500000000000 / 1232252638653) := by
    rw [show ((1232252638653 / 500000000000) : ℝ) = ((500000000000 / 1232252638653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13738_neg : (908843749 / 1000000000) ≤ -Real.log (100000000000 / 248145169573) ∧
    -Real.log (100000000000 / 248145169573) ≤ (908843751 / 1000000000) := by
  have h := checkLog_sound (w := (48145169573 / 448145169573)) (n := 12)
    (lo := (215696569 / 1000000000)) (hi := (21569657 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((248145169573 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(248145169573 / 200000000000) = 1/(100000000000 / 248145169573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13738 : Bounds (908843749 / 1000000000) (908843751 / 1000000000) (Real.log (248145169573 / 100000000000)) := by
  have h := reflection_log_13738_neg
  have he : Real.log (248145169573 / 100000000000) = -Real.log (100000000000 / 248145169573) := by
    rw [show ((248145169573 / 100000000000) : ℝ) = ((100000000000 / 248145169573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13739_neg : (488771131 / 250000000) ≤ -Real.log (125000000000 / 883064516129) ∧
    -Real.log (125000000000 / 883064516129) ≤ (1955084527 / 1000000000) := by
  have h := checkLog_sound (w := (383064516129 / 1383064516129)) (n := 12)
    (lo := (142197541 / 250000000)) (hi := (113758033 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((883064516129 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(883064516129 / 500000000000) = 1/(125000000000 / 883064516129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13739 : Bounds (488771131 / 250000000) (1955084527 / 1000000000) (Real.log (883064516129 / 125000000000)) := by
  have h := reflection_log_13739_neg
  have he : Real.log (883064516129 / 125000000000) = -Real.log (125000000000 / 883064516129) := by
    rw [show ((883064516129 / 125000000000) : ℝ) = ((125000000000 / 883064516129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13740_neg : (492241481 / 250000000) ≤ -Real.log (250000000000 / 1790816326531) ∧
    -Real.log (250000000000 / 1790816326531) ≤ (1968965927 / 1000000000) := by
  have h := checkLog_sound (w := (790816326531 / 2790816326531)) (n := 12)
    (lo := (145667891 / 250000000)) (hi := (116534313 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1790816326531 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1790816326531 / 1000000000000) = 1/(250000000000 / 1790816326531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13740 : Bounds (492241481 / 250000000) (1968965927 / 1000000000) (Real.log (1790816326531 / 250000000000)) := by
  have h := reflection_log_13740_neg
  have he : Real.log (1790816326531 / 250000000000) = -Real.log (250000000000 / 1790816326531) := by
    rw [show ((1790816326531 / 250000000000) : ℝ) = ((250000000000 / 1790816326531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13741_neg : (564176799 / 1000000000) ≤ -Real.log (500 / 879) ∧
    -Real.log (500 / 879) ≤ (705221 / 1250000) := by
  have h := checkLog_sound (w := (379 / 1379)) (n := 12)
    (lo := (564176799 / 1000000000)) (hi := (705221 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((879 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(879 / 500) = 1/(500 / 879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13741 : Bounds (564176799 / 1000000000) (705221 / 1250000) (Real.log (879 / 500)) := by
  have h := reflection_log_13741_neg
  have he : Real.log (879 / 500) = -Real.log (500 / 879) := by
    rw [show ((879 / 500) : ℝ) = ((500 / 879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13742_neg : (1418817551 / 1000000000) ≤ -Real.log (121 / 500) ∧
    -Real.log (121 / 500) ≤ (709408777 / 500000000) := by
  have h := checkLog_sound (w := (2 / 123)) (n := 12)
    (lo := (32523191 / 1000000000)) (hi := (4065399 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 121) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 121) = 1/(121 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13742 : Bounds (-709408777 / 500000000) (-1418817551 / 1000000000) (Real.log (121 / 500)) := by
  have h := reflection_log_13742_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13743_neg : (47357 / 62500000) ≤ -Real.log (500000 / 500379) ∧
    -Real.log (500000 / 500379) ≤ (757713 / 1000000000) := by
  have h := checkLog_sound (w := (379 / 1000379)) (n := 12)
    (lo := (47357 / 62500000)) (hi := (757713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500379 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500379 / 500000) = 1/(500000 / 500379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13743 : Bounds (47357 / 62500000) (757713 / 1000000000) (Real.log (500379 / 500000)) := by
  have h := reflection_log_13743_neg
  have he : Real.log (500379 / 500000) = -Real.log (500000 / 500379) := by
    rw [show ((500379 / 500000) : ℝ) = ((500000 / 500379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13744_neg : (758287 / 1000000000) ≤ -Real.log (499621 / 500000) ∧
    -Real.log (499621 / 500000) ≤ (47393 / 62500000) := by
  have h := checkLog_sound (w := (379 / 999621)) (n := 12)
    (lo := (758287 / 1000000000)) (hi := (47393 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499621) = 1/(499621 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13744 : Bounds (-47393 / 62500000) (-758287 / 1000000000) (Real.log (499621 / 500000)) := by
  have h := reflection_log_13744_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13745_neg : (354089003 / 1000000000) ≤ -Real.log (500000 / 712441) ∧
    -Real.log (500000 / 712441) ≤ (88522251 / 250000000) := by
  have h := checkLog_sound (w := (212441 / 1212441)) (n := 12)
    (lo := (354089003 / 1000000000)) (hi := (88522251 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((712441 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(712441 / 500000) = 1/(500000 / 712441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13745 : Bounds (354089003 / 1000000000) (88522251 / 250000000) (Real.log (712441 / 500000)) := by
  have h := reflection_log_13745_neg
  have he : Real.log (712441 / 500000) = -Real.log (500000 / 712441) := by
    rw [show ((712441 / 500000) : ℝ) = ((500000 / 712441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13746_neg : (553180041 / 1000000000) ≤ -Real.log (287559 / 500000) ∧
    -Real.log (287559 / 500000) ≤ (276590021 / 500000000) := by
  have h := checkLog_sound (w := (212441 / 787559)) (n := 12)
    (lo := (553180041 / 1000000000)) (hi := (276590021 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 287559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 287559) = 1/(287559 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13746 : Bounds (-276590021 / 500000000) (-553180041 / 1000000000) (Real.log (287559 / 500000)) := by
  have h := reflection_log_13746_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13747_neg : (178033079 / 500000000) ≤ -Real.log (500000 / 713851) ∧
    -Real.log (500000 / 713851) ≤ (356066159 / 1000000000) := by
  have h := checkLog_sound (w := (213851 / 1213851)) (n := 12)
    (lo := (178033079 / 500000000)) (hi := (356066159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((713851 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(713851 / 500000) = 1/(500000 / 713851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13747 : Bounds (178033079 / 500000000) (356066159 / 1000000000) (Real.log (713851 / 500000)) := by
  have h := reflection_log_13747_neg
  have he : Real.log (713851 / 500000) = -Real.log (500000 / 713851) := by
    rw [show ((713851 / 500000) : ℝ) = ((500000 / 713851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13748_neg : (139523861 / 250000000) ≤ -Real.log (286149 / 500000) ∧
    -Real.log (286149 / 500000) ≤ (111619089 / 200000000) := by
  have h := checkLog_sound (w := (213851 / 786149)) (n := 12)
    (lo := (139523861 / 250000000)) (hi := (111619089 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 286149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 286149) = 1/(286149 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13748 : Bounds (-111619089 / 200000000) (-139523861 / 250000000) (Real.log (286149 / 500000)) := by
  have h := reflection_log_13748_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13749_neg : (40405857 / 200000000) ≤ -Real.log (204267749799 / 250000000000) ∧
    -Real.log (204267749799 / 250000000000) ≤ (101014643 / 500000000) := by
  have h := checkLog_sound (w := (45732250201 / 454267749799)) (n := 12)
    (lo := (40405857 / 200000000)) (hi := (101014643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 204267749799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 204267749799) = 1/(204267749799 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13749 : Bounds (-101014643 / 500000000) (-40405857 / 200000000) (Real.log (204267749799 / 250000000000)) := by
  have h := reflection_log_13749_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13750_neg : (99545519 / 500000000) ≤ -Real.log (204868821519 / 250000000000) ∧
    -Real.log (204868821519 / 250000000000) ≤ (199091039 / 1000000000) := by
  have h := checkLog_sound (w := (45131178481 / 454868821519)) (n := 12)
    (lo := (99545519 / 500000000)) (hi := (199091039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 204868821519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 204868821519) = 1/(204868821519 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13750 : Bounds (-199091039 / 1000000000) (-99545519 / 500000000) (Real.log (204868821519 / 250000000000)) := by
  have h := reflection_log_13750_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13751_neg : (226817261 / 250000000) ≤ -Real.log (250000000000 / 619386804099) ∧
    -Real.log (250000000000 / 619386804099) ≤ (453634523 / 500000000) := by
  have h := checkLog_sound (w := (119386804099 / 1119386804099)) (n := 12)
    (lo := (26765233 / 125000000)) (hi := (42824373 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((619386804099 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(619386804099 / 500000000000) = 1/(250000000000 / 619386804099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13751 : Bounds (226817261 / 250000000) (453634523 / 500000000) (Real.log (619386804099 / 250000000000)) := by
  have h := reflection_log_13751_neg
  have he : Real.log (619386804099 / 250000000000) = -Real.log (250000000000 / 619386804099) := by
    rw [show ((619386804099 / 250000000000) : ℝ) = ((250000000000 / 619386804099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13752_neg : (457080801 / 500000000) ≤ -Real.log (50000000000 / 124734142003) ∧
    -Real.log (50000000000 / 124734142003) ≤ (228540401 / 250000000) := by
  have h := checkLog_sound (w := (24734142003 / 224734142003)) (n := 12)
    (lo := (110507211 / 500000000)) (hi := (221014423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((124734142003 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(124734142003 / 100000000000) = 1/(50000000000 / 124734142003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13752 : Bounds (457080801 / 500000000) (228540401 / 250000000) (Real.log (124734142003 / 50000000000)) := by
  have h := reflection_log_13752_neg
  have he : Real.log (124734142003 / 50000000000) = -Real.log (50000000000 / 124734142003) := by
    rw [show ((124734142003 / 50000000000) : ℝ) = ((50000000000 / 124734142003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13753_neg : (492241481 / 250000000) ≤ -Real.log (500000000000 / 3581632653061) ∧
    -Real.log (500000000000 / 3581632653061) ≤ (1968965927 / 1000000000) := by
  have h := checkLog_sound (w := (1581632653061 / 5581632653061)) (n := 12)
    (lo := (145667891 / 250000000)) (hi := (116534313 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3581632653061 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3581632653061 / 2000000000000) = 1/(500000000000 / 3581632653061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13753 : Bounds (492241481 / 250000000) (1968965927 / 1000000000) (Real.log (3581632653061 / 500000000000)) := by
  have h := reflection_log_13753_neg
  have he : Real.log (3581632653061 / 500000000000) = -Real.log (500000000000 / 3581632653061) := by
    rw [show ((3581632653061 / 500000000000) : ℝ) = ((500000000000 / 3581632653061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13754_neg : (39659887 / 20000000) ≤ -Real.log (500000000000 / 3632231404959) ∧
    -Real.log (500000000000 / 3632231404959) ≤ (1982994353 / 1000000000) := by
  have h := checkLog_sound (w := (1632231404959 / 5632231404959)) (n := 12)
    (lo := (59669999 / 100000000)) (hi := (596699991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3632231404959 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3632231404959 / 2000000000000) = 1/(500000000000 / 3632231404959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13754 : Bounds (39659887 / 20000000) (1982994353 / 1000000000) (Real.log (3632231404959 / 500000000000)) := by
  have h := reflection_log_13754_neg
  have he : Real.log (3632231404959 / 500000000000) = -Real.log (500000000000 / 3632231404959) := by
    rw [show ((3632231404959 / 500000000000) : ℝ) = ((500000000000 / 3632231404959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13755_neg : (565881829 / 1000000000) ≤ -Real.log (1000 / 1761) ∧
    -Real.log (1000 / 1761) ≤ (56588183 / 100000000) := by
  have h := checkLog_sound (w := (761 / 2761)) (n := 12)
    (lo := (565881829 / 1000000000)) (hi := (56588183 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1761 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1761 / 1000) = 1/(1000 / 1761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13755 : Bounds (565881829 / 1000000000) (56588183 / 100000000) (Real.log (1761 / 1000)) := by
  have h := reflection_log_13755_neg
  have he : Real.log (1761 / 1000) = -Real.log (1000 / 1761) := by
    rw [show ((1761 / 1000) : ℝ) = ((1000 / 1761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13756_neg : (57251669 / 40000000) ≤ -Real.log (239 / 1000) ∧
    -Real.log (239 / 1000) ≤ (89455733 / 62500000) := by
  have h := checkLog_sound (w := (11 / 489)) (n := 12)
    (lo := (8999473 / 200000000)) (hi := (22498683 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 239) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 239) = 1/(239 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13756 : Bounds (-89455733 / 62500000) (-57251669 / 40000000) (Real.log (239 / 1000)) := by
  have h := reflection_log_13756_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13757_neg : (76071 / 100000000) ≤ -Real.log (1000000 / 1000761) ∧
    -Real.log (1000000 / 1000761) ≤ (760711 / 1000000000) := by
  have h := checkLog_sound (w := (761 / 2000761)) (n := 12)
    (lo := (76071 / 100000000)) (hi := (760711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000761 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000761 / 1000000) = 1/(1000000 / 1000761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13757 : Bounds (76071 / 100000000) (760711 / 1000000000) (Real.log (1000761 / 1000000)) := by
  have h := reflection_log_13757_neg
  have he : Real.log (1000761 / 1000000) = -Real.log (1000000 / 1000761) := by
    rw [show ((1000761 / 1000000) : ℝ) = ((1000000 / 1000761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13758_neg : (761289 / 1000000000) ≤ -Real.log (999239 / 1000000) ∧
    -Real.log (999239 / 1000000) ≤ (76129 / 100000000) := by
  have h := checkLog_sound (w := (761 / 1999239)) (n := 12)
    (lo := (761289 / 1000000000)) (hi := (76129 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999239) = 1/(999239 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13758 : Bounds (-76129 / 100000000) (-761289 / 1000000000) (Real.log (999239 / 1000000)) := by
  have h := reflection_log_13758_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13759_neg : (17780679 / 50000000) ≤ -Real.log (62500 / 89191) ∧
    -Real.log (62500 / 89191) ≤ (355613581 / 1000000000) := by
  have h := checkLog_sound (w := (26691 / 151691)) (n := 12)
    (lo := (17780679 / 50000000)) (hi := (355613581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89191 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89191 / 62500) = 1/(62500 / 89191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13759 : Bounds (17780679 / 50000000) (355613581 / 1000000000) (Real.log (89191 / 62500)) := by
  have h := reflection_log_13759_neg
  have he : Real.log (89191 / 62500) = -Real.log (62500 / 89191) := by
    rw [show ((89191 / 62500) : ℝ) = ((62500 / 89191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
