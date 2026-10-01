import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0203
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (582215619 / 1000000000) ≤ -Real.log (100 / 179) ∧
    -Real.log (100 / 179) ≤ (29110781 / 50000000) := by
  have h := checkLog_sound (w := (79 / 279)) (n := 12)
    (lo := (582215619 / 1000000000)) (hi := (29110781 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(179 / 100) = 1/(100 / 179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (582215619 / 1000000000) (29110781 / 50000000) (Real.log (179 / 100)) := by
  have h := reflection_log_1_neg
  have he : Real.log (179 / 100) = -Real.log (100 / 179) := by
    rw [show ((179 / 100) : ℝ) = ((100 / 179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (1560647747 / 1000000000) ≤ -Real.log (21 / 100) ∧
    -Real.log (21 / 100) ≤ (6242591 / 4000000) := by
  have h := checkLog_sound (w := (2 / 23)) (n := 12)
    (lo := (174353387 / 1000000000)) (hi := (43588347 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 21) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(25 / 21) = 1/(21 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-6242591 / 4000000) (-1560647747 / 1000000000) (Real.log (21 / 100)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (578893067 / 1000000000) ≤ -Real.log (3200 / 5709) ∧
    -Real.log (3200 / 5709) ≤ (144723267 / 250000000) := by
  have h := checkLog_sound (w := (2509 / 8909)) (n := 12)
    (lo := (578893067 / 1000000000)) (hi := (144723267 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5709 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5709 / 3200) = 1/(3200 / 5709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (578893067 / 1000000000) (144723267 / 250000000) (Real.log (5709 / 3200)) := by
  have h := reflection_log_3_neg
  have he : Real.log (5709 / 3200) = -Real.log (3200 / 5709) := by
    rw [show ((5709 / 3200) : ℝ) = ((3200 / 5709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1532766263 / 1000000000) ≤ -Real.log (691 / 3200) ∧
    -Real.log (691 / 3200) ≤ (766383133 / 500000000) := by
  have h := checkLog_sound (w := (109 / 1491)) (n := 12)
    (lo := (146471903 / 1000000000)) (hi := (4577247 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 691) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(800 / 691) = 1/(691 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-766383133 / 500000000) (-1532766263 / 1000000000) (Real.log (691 / 3200)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (457424847 / 1000000000) ≤ -Real.log (50 / 79) ∧
    -Real.log (50 / 79) ≤ (28589053 / 62500000) := by
  have h := checkLog_sound (w := (29 / 129)) (n := 12)
    (lo := (457424847 / 1000000000)) (hi := (28589053 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79 / 50) = 1/(50 / 79) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (457424847 / 1000000000) (28589053 / 62500000) (Real.log (79 / 50)) := by
  have h := reflection_log_5_neg
  have he : Real.log (79 / 50) = -Real.log (50 / 79) := by
    rw [show ((79 / 50) : ℝ) = ((50 / 79) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (867500567 / 1000000000) ≤ -Real.log (21 / 50) ∧
    -Real.log (21 / 50) ≤ (867500569 / 1000000000) := by
  have h := checkLog_sound (w := (2 / 23)) (n := 12)
    (lo := (174353387 / 1000000000)) (hi := (43588347 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 21) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25 / 21) = 1/(21 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-867500569 / 1000000000) (-867500567 / 1000000000) (Real.log (21 / 50)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (224940319 / 500000000) ≤ -Real.log (1600 / 2509) ∧
    -Real.log (1600 / 2509) ≤ (449880639 / 1000000000) := by
  have h := checkLog_sound (w := (909 / 4109)) (n := 12)
    (lo := (224940319 / 500000000)) (hi := (449880639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2509 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2509 / 1600) = 1/(1600 / 2509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (224940319 / 500000000) (449880639 / 1000000000) (Real.log (2509 / 1600)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2509 / 1600) = -Real.log (1600 / 2509) := by
    rw [show ((2509 / 1600) : ℝ) = ((1600 / 2509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (839619083 / 1000000000) ≤ -Real.log (691 / 1600) ∧
    -Real.log (691 / 1600) ≤ (167923817 / 200000000) := by
  have h := checkLog_sound (w := (109 / 1491)) (n := 12)
    (lo := (146471903 / 1000000000)) (hi := (4577247 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 691) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(800 / 691) = 1/(691 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-167923817 / 200000000) (-839619083 / 1000000000) (Real.log (691 / 1600)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (308772777 / 500000000) ≤ -Real.log (1000000 / 1854371) ∧
    -Real.log (1000000 / 1854371) ≤ (123509111 / 200000000) := by
  have h := checkLog_sound (w := (854371 / 2854371)) (n := 12)
    (lo := (308772777 / 500000000)) (hi := (123509111 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1854371 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1854371 / 1000000) = 1/(1000000 / 1854371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (308772777 / 500000000) (123509111 / 200000000) (Real.log (1854371 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1854371 / 1000000) = -Real.log (1000000 / 1854371) := by
    rw [show ((1854371 / 1000000) : ℝ) = ((1000000 / 1854371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (963346493 / 500000000) ≤ -Real.log (145629 / 1000000) ∧
    -Real.log (145629 / 1000000) ≤ (1926692989 / 1000000000) := by
  have h := checkLog_sound (w := (104371 / 395629)) (n := 12)
    (lo := (270199313 / 500000000)) (hi := (540398627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 145629) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 145629) = 1/(145629 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1926692989 / 1000000000) (-963346493 / 500000000) (Real.log (145629 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (123836501 / 200000000) ≤ -Real.log (1000000 / 1857409) ∧
    -Real.log (1000000 / 1857409) ≤ (309591253 / 500000000) := by
  have h := checkLog_sound (w := (857409 / 2857409)) (n := 12)
    (lo := (123836501 / 200000000)) (hi := (309591253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1857409 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1857409 / 1000000) = 1/(1000000 / 1857409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (123836501 / 200000000) (309591253 / 500000000) (Real.log (1857409 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1857409 / 1000000) = -Real.log (1000000 / 1857409) := by
    rw [show ((1857409 / 1000000) : ℝ) = ((1000000 / 1857409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (389554977 / 200000000) ≤ -Real.log (142591 / 1000000) ∧
    -Real.log (142591 / 1000000) ≤ (243471861 / 125000000) := by
  have h := checkLog_sound (w := (107409 / 392591)) (n := 12)
    (lo := (22459221 / 40000000)) (hi := (280740263 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 142591) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 142591) = 1/(142591 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-243471861 / 125000000) (-389554977 / 200000000) (Real.log (142591 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (38095027 / 62500000) ≤ -Real.log (1000000 / 1839549) ∧
    -Real.log (1000000 / 1839549) ≤ (609520433 / 1000000000) := by
  have h := checkLog_sound (w := (839549 / 2839549)) (n := 12)
    (lo := (38095027 / 62500000)) (hi := (609520433 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1839549 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1839549 / 1000000) = 1/(1000000 / 1839549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (38095027 / 62500000) (609520433 / 1000000000) (Real.log (1839549 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1839549 / 1000000) = -Real.log (1000000 / 1839549) := by
    rw [show ((1839549 / 1000000) : ℝ) = ((1000000 / 1839549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1829766677 / 1000000000) ≤ -Real.log (160451 / 1000000) ∧
    -Real.log (160451 / 1000000) ≤ (45744167 / 25000000) := by
  have h := checkLog_sound (w := (89549 / 410451)) (n := 12)
    (lo := (443472317 / 1000000000)) (hi := (221736159 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 160451) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 160451) = 1/(160451 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-45744167 / 25000000) (-1829766677 / 1000000000) (Real.log (160451 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (152924621 / 250000000) ≤ -Real.log (25000 / 46089) ∧
    -Real.log (25000 / 46089) ≤ (122339697 / 200000000) := by
  have h := checkLog_sound (w := (21089 / 71089)) (n := 12)
    (lo := (152924621 / 250000000)) (hi := (122339697 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((46089 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(46089 / 25000) = 1/(25000 / 46089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (152924621 / 250000000) (122339697 / 200000000) (Real.log (46089 / 25000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (46089 / 25000) = -Real.log (25000 / 46089) := by
    rw [show ((46089 / 25000) : ℝ) = ((25000 / 46089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1855082727 / 1000000000) ≤ -Real.log (3911 / 25000) ∧
    -Real.log (3911 / 25000) ≤ (185508273 / 100000000) := by
  have h := checkLog_sound (w := (2339 / 10161)) (n := 12)
    (lo := (468788367 / 1000000000)) (hi := (29299273 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 3911) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(6250 / 3911) = 1/(3911 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-185508273 / 100000000) (-1855082727 / 1000000000) (Real.log (3911 / 25000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (127211927 / 50000000) ≤ -Real.log (500000000000 / 6366764174717) ∧
    -Real.log (500000000000 / 6366764174717) ≤ (159014909 / 62500000) := by
  have h := checkLog_sound (w := (2366764174717 / 10366764174717)) (n := 12)
    (lo := (464797 / 1000000)) (hi := (464797001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6366764174717 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6366764174717 / 4000000000000) = 1/(500000000000 / 6366764174717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (127211927 / 50000000) (159014909 / 62500000) (Real.log (6366764174717 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (6366764174717 / 500000000000) = -Real.log (500000000000 / 6366764174717) := by
    rw [show ((6366764174717 / 500000000000) : ℝ) = ((500000000000 / 6366764174717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (256695739 / 100000000) ≤ -Real.log (50000000000 / 651306534073) ∧
    -Real.log (50000000000 / 651306534073) ≤ (1283478697 / 500000000) := by
  have h := checkLog_sound (w := (251306534073 / 1051306534073)) (n := 12)
    (lo := (9750317 / 20000000)) (hi := (487515851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((651306534073 / 400000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(651306534073 / 400000000000) = 1/(50000000000 / 651306534073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (256695739 / 100000000) (1283478697 / 500000000) (Real.log (651306534073 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (651306534073 / 50000000000) = -Real.log (50000000000 / 651306534073) := by
    rw [show ((651306534073 / 50000000000) : ℝ) = ((50000000000 / 651306534073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (243928711 / 100000000) ≤ -Real.log (100000000000 / 1146486466273) ∧
    -Real.log (100000000000 / 1146486466273) ≤ (1219643557 / 500000000) := by
  have h := checkLog_sound (w := (346486466273 / 1946486466273)) (n := 12)
    (lo := (35984557 / 100000000)) (hi := (359845571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1146486466273 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1146486466273 / 800000000000) = 1/(100000000000 / 1146486466273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (243928711 / 100000000) (1219643557 / 500000000) (Real.log (1146486466273 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1146486466273 / 100000000000) = -Real.log (100000000000 / 1146486466273) := by
    rw [show ((1146486466273 / 100000000000) : ℝ) = ((100000000000 / 1146486466273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (616695303 / 250000000) ≤ -Real.log (100000000000 / 1178445410381) ∧
    -Real.log (100000000000 / 1178445410381) ≤ (77086913 / 31250000) := by
  have h := checkLog_sound (w := (378445410381 / 1978445410381)) (n := 12)
    (lo := (48417459 / 125000000)) (hi := (387339673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1178445410381 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1178445410381 / 800000000000) = 1/(100000000000 / 1178445410381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (616695303 / 250000000) (77086913 / 31250000) (Real.log (1178445410381 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1178445410381 / 100000000000) = -Real.log (100000000000 / 1178445410381) := by
    rw [show ((1178445410381 / 100000000000) : ℝ) = ((100000000000 / 1178445410381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0203
