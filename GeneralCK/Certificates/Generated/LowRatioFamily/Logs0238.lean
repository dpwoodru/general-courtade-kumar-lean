import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_15232_neg : (124016813 / 250000000) ≤ -Real.log (4000 / 6569) ∧
    -Real.log (4000 / 6569) ≤ (496067253 / 1000000000) := by
  have h := checkLog_sound (w := (2569 / 10569)) (n := 12)
    (lo := (124016813 / 250000000)) (hi := (496067253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6569 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6569 / 4000) = 1/(4000 / 6569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15232 : Bounds (124016813 / 250000000) (496067253 / 1000000000) (Real.log (6569 / 4000)) := by
  have h := reflection_log_15232_neg
  have he : Real.log (6569 / 4000) = -Real.log (4000 / 6569) := by
    rw [show ((6569 / 4000) : ℝ) = ((4000 / 6569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15233_neg : (1027920859 / 1000000000) ≤ -Real.log (1431 / 4000) ∧
    -Real.log (1431 / 4000) ≤ (1027920861 / 1000000000) := by
  have h := checkLog_sound (w := (569 / 3431)) (n := 12)
    (lo := (334773679 / 1000000000)) (hi := (4184671 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1431) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2000 / 1431) = 1/(1431 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15233 : Bounds (-1027920861 / 1000000000) (-1027920859 / 1000000000) (Real.log (1431 / 4000)) := by
  have h := reflection_log_15233_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15234_neg : (248315477 / 500000000) ≤ -Real.log (125000 / 205397) ∧
    -Real.log (125000 / 205397) ≤ (99326191 / 200000000) := by
  have h := checkLog_sound (w := (80397 / 330397)) (n := 12)
    (lo := (248315477 / 500000000)) (hi := (99326191 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((205397 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(205397 / 125000) = 1/(125000 / 205397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15234 : Bounds (248315477 / 500000000) (99326191 / 200000000) (Real.log (205397 / 125000)) := by
  have h := reflection_log_15234_neg
  have he : Real.log (205397 / 125000) = -Real.log (125000 / 205397) := by
    rw [show ((205397 / 125000) : ℝ) = ((125000 / 205397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15235_neg : (206102523 / 200000000) ≤ -Real.log (44603 / 125000) ∧
    -Real.log (44603 / 125000) ≤ (1030512617 / 1000000000) := by
  have h := checkLog_sound (w := (17897 / 107103)) (n := 12)
    (lo := (67473087 / 200000000)) (hi := (84341359 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 44603) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 44603) = 1/(44603 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15235 : Bounds (-1030512617 / 1000000000) (-206102523 / 200000000) (Real.log (44603 / 125000)) := by
  have h := reflection_log_15235_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15236_neg : (533881661 / 1000000000) ≤ -Real.log (9161322391 / 15625000000) ∧
    -Real.log (9161322391 / 15625000000) ≤ (266940831 / 500000000) := by
  have h := checkLog_sound (w := (6463677609 / 24786322391)) (n := 12)
    (lo := (533881661 / 1000000000)) (hi := (266940831 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 9161322391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 9161322391) = 1/(9161322391 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15236 : Bounds (-266940831 / 500000000) (-533881661 / 1000000000) (Real.log (9161322391 / 15625000000)) := by
  have h := reflection_log_15236_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15237_neg : (531853607 / 1000000000) ≤ -Real.log (9400239 / 16000000) ∧
    -Real.log (9400239 / 16000000) ≤ (66481701 / 125000000) := by
  have h := checkLog_sound (w := (6599761 / 25400239)) (n := 12)
    (lo := (531853607 / 1000000000)) (hi := (66481701 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16000000 / 9400239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16000000 / 9400239) = 1/(9400239 / 16000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15237 : Bounds (-66481701 / 125000000) (-531853607 / 1000000000) (Real.log (9400239 / 16000000)) := by
  have h := reflection_log_15237_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15238_neg : (95249257 / 62500000) ≤ -Real.log (250000000000 / 1147624039133) ∧
    -Real.log (250000000000 / 1147624039133) ≤ (304797623 / 200000000) := by
  have h := checkLog_sound (w := (147624039133 / 2147624039133)) (n := 12)
    (lo := (17211719 / 125000000)) (hi := (137693753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1147624039133 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1147624039133 / 1000000000000) = 1/(250000000000 / 1147624039133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15238 : Bounds (95249257 / 62500000) (304797623 / 200000000) (Real.log (1147624039133 / 250000000000)) := by
  have h := reflection_log_15238_neg
  have he : Real.log (1147624039133 / 250000000000) = -Real.log (250000000000 / 1147624039133) := by
    rw [show ((1147624039133 / 250000000000) : ℝ) = ((250000000000 / 1147624039133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15239_neg : (1527143569 / 1000000000) ≤ -Real.log (125000000000 / 575625518463) ∧
    -Real.log (125000000000 / 575625518463) ≤ (381785893 / 250000000) := by
  have h := checkLog_sound (w := (75625518463 / 1075625518463)) (n := 12)
    (lo := (140849209 / 1000000000)) (hi := (14084921 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((575625518463 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(575625518463 / 500000000000) = 1/(125000000000 / 575625518463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15239 : Bounds (1527143569 / 1000000000) (381785893 / 250000000) (Real.log (575625518463 / 125000000000)) := by
  have h := reflection_log_15239_neg
  have he : Real.log (575625518463 / 125000000000) = -Real.log (125000000000 / 575625518463) := by
    rw [show ((575625518463 / 125000000000) : ℝ) = ((125000000000 / 575625518463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15240_neg : (26671639 / 5000000) ≤ -Real.log (250000000000 / 51833333333333) ∧
    -Real.log (250000000000 / 51833333333333) ≤ (10418609 / 1953125) := by
  have h := checkLog_sound (w := (19833333333333 / 83833333333333)) (n := 12)
    (lo := (24114877 / 50000000)) (hi := (482297541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51833333333333 / 32000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(51833333333333 / 32000000000000) = 1/(250000000000 / 51833333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15240 : Bounds (26671639 / 5000000) (10418609 / 1953125) (Real.log (51833333333333 / 250000000000)) := by
  have h := reflection_log_15240_neg
  have he : Real.log (51833333333333 / 250000000000) = -Real.log (250000000000 / 51833333333333) := by
    rw [show ((51833333333333 / 250000000000) : ℝ) = ((250000000000 / 51833333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15241_neg : (2677740843 / 500000000) ≤ -Real.log (100000000000 / 21176595744681) ∧
    -Real.log (100000000000 / 21176595744681) ≤ (2677740847 / 500000000) := by
  have h := checkLog_sound (w := (8376595744681 / 33976595744681)) (n := 12)
    (lo := (251725713 / 500000000)) (hi := (503451427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21176595744681 / 12800000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(21176595744681 / 12800000000000) = 1/(100000000000 / 21176595744681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15241 : Bounds (2677740843 / 500000000) (2677740847 / 500000000) (Real.log (21176595744681 / 100000000000)) := by
  have h := reflection_log_15241_neg
  have he : Real.log (21176595744681 / 100000000000) = -Real.log (100000000000 / 21176595744681) := by
    rw [show ((21176595744681 / 100000000000) : ℝ) = ((100000000000 / 21176595744681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15242_neg : (86067071 / 125000000) ≤ -Real.log (2500 / 4977) ∧
    -Real.log (2500 / 4977) ≤ (688536569 / 1000000000) := by
  have h := checkLog_sound (w := (2477 / 7477)) (n := 12)
    (lo := (86067071 / 125000000)) (hi := (688536569 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4977 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4977 / 2500) = 1/(2500 / 4977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15242 : Bounds (86067071 / 125000000) (688536569 / 1000000000) (Real.log (4977 / 2500)) := by
  have h := reflection_log_15242_neg
  have he : Real.log (4977 / 2500) = -Real.log (2500 / 4977) := by
    rw [show ((4977 / 2500) : ℝ) = ((2500 / 4977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15243_neg : (4688551791 / 1000000000) ≤ -Real.log (23 / 2500) ∧
    -Real.log (23 / 2500) ≤ (2344275899 / 500000000) := by
  have h := checkLog_sound (w := (257 / 993)) (n := 12)
    (lo := (529668711 / 1000000000)) (hi := (66208589 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 368) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(625 / 368) = 1/(23 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15243 : Bounds (-2344275899 / 500000000) (-4688551791 / 1000000000) (Real.log (23 / 2500)) := by
  have h := reflection_log_15243_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15244_neg : (990309 / 1000000000) ≤ -Real.log (2500000 / 2502477) ∧
    -Real.log (2500000 / 2502477) ≤ (99031 / 100000000) := by
  have h := checkLog_sound (w := (2477 / 5002477)) (n := 12)
    (lo := (990309 / 1000000000)) (hi := (99031 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2502477 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2502477 / 2500000) = 1/(2500000 / 2502477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15244 : Bounds (990309 / 1000000000) (99031 / 100000000) (Real.log (2502477 / 2500000)) := by
  have h := reflection_log_15244_neg
  have he : Real.log (2502477 / 2500000) = -Real.log (2500000 / 2502477) := by
    rw [show ((2502477 / 2500000) : ℝ) = ((2500000 / 2502477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15245_neg : (991291 / 1000000000) ≤ -Real.log (2497523 / 2500000) ∧
    -Real.log (2497523 / 2500000) ≤ (247823 / 250000000) := by
  have h := checkLog_sound (w := (2477 / 4997523)) (n := 12)
    (lo := (991291 / 1000000000)) (hi := (247823 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2497523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2497523) = 1/(2497523 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15245 : Bounds (-247823 / 250000000) (-991291 / 1000000000) (Real.log (2497523 / 2500000)) := by
  have h := reflection_log_15245_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15246_neg : (496247477 / 1000000000) ≤ -Real.log (500000 / 821273) ∧
    -Real.log (500000 / 821273) ≤ (248123739 / 500000000) := by
  have h := checkLog_sound (w := (321273 / 1321273)) (n := 12)
    (lo := (496247477 / 1000000000)) (hi := (248123739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821273 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(821273 / 500000) = 1/(500000 / 821273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15246 : Bounds (496247477 / 1000000000) (248123739 / 500000000) (Real.log (821273 / 500000)) := by
  have h := reflection_log_15246_neg
  have he : Real.log (821273 / 500000) = -Real.log (500000 / 821273) := by
    rw [show ((821273 / 500000) : ℝ) = ((500000 / 821273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15247_neg : (205749719 / 200000000) ≤ -Real.log (178727 / 500000) ∧
    -Real.log (178727 / 500000) ≤ (1028748597 / 1000000000) := by
  have h := checkLog_sound (w := (71273 / 428727)) (n := 12)
    (lo := (67120283 / 200000000)) (hi := (41950177 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 178727) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 178727) = 1/(178727 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15247 : Bounds (-1028748597 / 1000000000) (-205749719 / 200000000) (Real.log (178727 / 500000)) := by
  have h := reflection_log_15247_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15248_neg : (496811077 / 1000000000) ≤ -Real.log (62500 / 102717) ∧
    -Real.log (62500 / 102717) ≤ (248405539 / 500000000) := by
  have h := checkLog_sound (w := (40217 / 165217)) (n := 12)
    (lo := (496811077 / 1000000000)) (hi := (248405539 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102717 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102717 / 62500) = 1/(62500 / 102717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15248 : Bounds (496811077 / 1000000000) (248405539 / 500000000) (Real.log (102717 / 62500)) := by
  have h := reflection_log_15248_neg
  have he : Real.log (102717 / 62500) = -Real.log (62500 / 102717) := by
    rw [show ((102717 / 62500) : ℝ) = ((62500 / 102717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15249_neg : (412537 / 400000) ≤ -Real.log (22283 / 62500) ∧
    -Real.log (22283 / 62500) ≤ (515671251 / 500000000) := by
  have h := checkLog_sound (w := (8967 / 53533)) (n := 12)
    (lo := (8454883 / 25000000)) (hi := (338195321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22283) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 22283) = 1/(22283 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15249 : Bounds (-515671251 / 500000000) (-412537 / 400000) (Real.log (22283 / 62500)) := by
  have h := reflection_log_15249_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15250_neg : (534531423 / 1000000000) ≤ -Real.log (2288842911 / 3906250000) ∧
    -Real.log (2288842911 / 3906250000) ≤ (16704107 / 31250000) := by
  have h := checkLog_sound (w := (1617407089 / 6195092911)) (n := 12)
    (lo := (534531423 / 1000000000)) (hi := (16704107 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 2288842911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 2288842911) = 1/(2288842911 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15250 : Bounds (-16704107 / 31250000) (-534531423 / 1000000000) (Real.log (2288842911 / 3906250000)) := by
  have h := reflection_log_15250_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15251_neg : (532501119 / 1000000000) ≤ -Real.log (146783659471 / 250000000000) ∧
    -Real.log (146783659471 / 250000000000) ≤ (832033 / 1562500) := by
  have h := checkLog_sound (w := (103216340529 / 396783659471)) (n := 12)
    (lo := (532501119 / 1000000000)) (hi := (832033 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 146783659471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 146783659471) = 1/(146783659471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15251 : Bounds (-832033 / 1562500) (-532501119 / 1000000000) (Real.log (146783659471 / 250000000000)) := by
  have h := reflection_log_15251_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15252_neg : (190624509 / 125000000) ≤ -Real.log (12500000000 / 57439069083) ∧
    -Real.log (12500000000 / 57439069083) ≤ (60999843 / 40000000) := by
  have h := checkLog_sound (w := (7439069083 / 107439069083)) (n := 12)
    (lo := (8668857 / 62500000)) (hi := (138701713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((57439069083 / 50000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(57439069083 / 50000000000) = 1/(12500000000 / 57439069083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15252 : Bounds (190624509 / 125000000) (60999843 / 40000000) (Real.log (57439069083 / 12500000000)) := by
  have h := reflection_log_15252_neg
  have he : Real.log (57439069083 / 12500000000) = -Real.log (12500000000 / 57439069083) := by
    rw [show ((57439069083 / 12500000000) : ℝ) = ((12500000000 / 57439069083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15253_neg : (191019197 / 125000000) ≤ -Real.log (500000000000 / 2304828793251) ∧
    -Real.log (500000000000 / 2304828793251) ≤ (1528153579 / 1000000000) := by
  have h := checkLog_sound (w := (304828793251 / 4304828793251)) (n := 12)
    (lo := (8866201 / 62500000)) (hi := (141859217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2304828793251 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2304828793251 / 2000000000000) = 1/(500000000000 / 2304828793251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15253 : Bounds (191019197 / 125000000) (1528153579 / 1000000000) (Real.log (2304828793251 / 500000000000)) := by
  have h := reflection_log_15253_neg
  have he : Real.log (2304828793251 / 500000000000) = -Real.log (500000000000 / 2304828793251) := by
    rw [show ((2304828793251 / 500000000000) : ℝ) = ((500000000000 / 2304828793251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15254_neg : (2677740843 / 500000000) ≤ -Real.log (125000000000 / 26470744680851) ∧
    -Real.log (125000000000 / 26470744680851) ≤ (2677740847 / 500000000) := by
  have h := checkLog_sound (w := (10470744680851 / 42470744680851)) (n := 12)
    (lo := (251725713 / 500000000)) (hi := (503451427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((26470744680851 / 16000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(26470744680851 / 16000000000000) = 1/(125000000000 / 26470744680851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15254 : Bounds (2677740843 / 500000000) (2677740847 / 500000000) (Real.log (26470744680851 / 125000000000)) := by
  have h := reflection_log_15254_neg
  have he : Real.log (26470744680851 / 125000000000) = -Real.log (125000000000 / 26470744680851) := by
    rw [show ((26470744680851 / 125000000000) : ℝ) = ((125000000000 / 26470744680851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15255_neg : (5377088359 / 1000000000) ≤ -Real.log (250000000000 / 54097826086957) ∧
    -Real.log (250000000000 / 54097826086957) ≤ (5377088367 / 1000000000) := by
  have h := checkLog_sound (w := (22097826086957 / 86097826086957)) (n := 12)
    (lo := (525058099 / 1000000000)) (hi := (5250581 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54097826086957 / 32000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(54097826086957 / 32000000000000) = 1/(250000000000 / 54097826086957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15255 : Bounds (5377088359 / 1000000000) (5377088367 / 1000000000) (Real.log (54097826086957 / 250000000000)) := by
  have h := reflection_log_15255_neg
  have he : Real.log (54097826086957 / 250000000000) = -Real.log (250000000000 / 54097826086957) := by
    rw [show ((54097826086957 / 250000000000) : ℝ) = ((250000000000 / 54097826086957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15256_neg : (27545481 / 40000000) ≤ -Real.log (1000 / 1991) ∧
    -Real.log (1000 / 1991) ≤ (344318513 / 500000000) := by
  have h := checkLog_sound (w := (991 / 2991)) (n := 12)
    (lo := (27545481 / 40000000)) (hi := (344318513 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1991 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1991 / 1000) = 1/(1000 / 1991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15256 : Bounds (27545481 / 40000000) (344318513 / 500000000) (Real.log (1991 / 1000)) := by
  have h := reflection_log_15256_neg
  have he : Real.log (1991 / 1000) = -Real.log (1000 / 1991) := by
    rw [show ((1991 / 1000) : ℝ) = ((1000 / 1991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15257_neg : (2355265349 / 500000000) ≤ -Real.log (9 / 1000) ∧
    -Real.log (9 / 1000) ≤ (942106141 / 200000000) := by
  have h := checkLog_sound (w := (53 / 197)) (n := 12)
    (lo := (275823809 / 500000000)) (hi := (551647619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 72) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(125 / 72) = 1/(9 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15257 : Bounds (-942106141 / 200000000) (-2355265349 / 500000000) (Real.log (9 / 1000)) := by
  have h := reflection_log_15257_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15258_neg : (990509 / 1000000000) ≤ -Real.log (1000000 / 1000991) ∧
    -Real.log (1000000 / 1000991) ≤ (99051 / 100000000) := by
  have h := checkLog_sound (w := (991 / 2000991)) (n := 12)
    (lo := (990509 / 1000000000)) (hi := (99051 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000991 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000991 / 1000000) = 1/(1000000 / 1000991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15258 : Bounds (990509 / 1000000000) (99051 / 100000000) (Real.log (1000991 / 1000000)) := by
  have h := reflection_log_15258_neg
  have he : Real.log (1000991 / 1000000) = -Real.log (1000000 / 1000991) := by
    rw [show ((1000991 / 1000000) : ℝ) = ((1000000 / 1000991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15259_neg : (991491 / 1000000000) ≤ -Real.log (999009 / 1000000) ∧
    -Real.log (999009 / 1000000) ≤ (247873 / 250000000) := by
  have h := checkLog_sound (w := (991 / 1999009)) (n := 12)
    (lo := (991491 / 1000000000)) (hi := (247873 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999009) = 1/(999009 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15259 : Bounds (-247873 / 250000000) (-991491 / 1000000000) (Real.log (999009 / 1000000)) := by
  have h := reflection_log_15259_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15260_neg : (496428277 / 1000000000) ≤ -Real.log (1000000 / 1642843) ∧
    -Real.log (1000000 / 1642843) ≤ (248214139 / 500000000) := by
  have h := checkLog_sound (w := (642843 / 2642843)) (n := 12)
    (lo := (496428277 / 1000000000)) (hi := (248214139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1642843 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1642843 / 1000000) = 1/(1000000 / 1642843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15260 : Bounds (496428277 / 1000000000) (248214139 / 500000000) (Real.log (1642843 / 1000000)) := by
  have h := reflection_log_15260_neg
  have he : Real.log (1642843 / 1000000) = -Real.log (1000000 / 1642843) := by
    rw [show ((1642843 / 1000000) : ℝ) = ((1000000 / 1642843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15261_neg : (1029579817 / 1000000000) ≤ -Real.log (357157 / 1000000) ∧
    -Real.log (357157 / 1000000) ≤ (1029579819 / 1000000000) := by
  have h := checkLog_sound (w := (142843 / 857157)) (n := 12)
    (lo := (336432637 / 1000000000)) (hi := (168216319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 357157) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 357157) = 1/(357157 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15261 : Bounds (-1029579819 / 1000000000) (-1029579817 / 1000000000) (Real.log (357157 / 1000000)) := by
  have h := reflection_log_15261_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15262_neg : (3882753 / 7812500) ≤ -Real.log (100000 / 164377) ∧
    -Real.log (100000 / 164377) ≤ (99398477 / 200000000) := by
  have h := checkLog_sound (w := (64377 / 264377)) (n := 12)
    (lo := (3882753 / 7812500)) (hi := (99398477 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((164377 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(164377 / 100000) = 1/(100000 / 164377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15262 : Bounds (3882753 / 7812500) (99398477 / 200000000) (Real.log (164377 / 100000)) := by
  have h := reflection_log_15262_neg
  have he : Real.log (164377 / 100000) = -Real.log (100000 / 164377) := by
    rw [show ((164377 / 100000) : ℝ) = ((100000 / 164377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15263_neg : (2015974 / 1953125) ≤ -Real.log (35623 / 100000) ∧
    -Real.log (35623 / 100000) ≤ (103217869 / 100000000) := by
  have h := checkLog_sound (w := (14377 / 85623)) (n := 12)
    (lo := (84757877 / 250000000)) (hi := (339031509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 35623) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 35623) = 1/(35623 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15263 : Bounds (-103217869 / 100000000) (-2015974 / 1953125) (Real.log (35623 / 100000)) := by
  have h := reflection_log_15263_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15264_neg : (107037261 / 200000000) ≤ -Real.log (5855601871 / 10000000000) ∧
    -Real.log (5855601871 / 10000000000) ≤ (267593153 / 500000000) := by
  have h := checkLog_sound (w := (4144398129 / 15855601871)) (n := 12)
    (lo := (107037261 / 200000000)) (hi := (267593153 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 5855601871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 5855601871) = 1/(5855601871 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15264 : Bounds (-267593153 / 500000000) (-107037261 / 200000000) (Real.log (5855601871 / 10000000000)) := by
  have h := reflection_log_15264_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15265_neg : (26657577 / 50000000) ≤ -Real.log (586752877351 / 1000000000000) ∧
    -Real.log (586752877351 / 1000000000000) ≤ (533151541 / 1000000000) := by
  have h := checkLog_sound (w := (413247122649 / 1586752877351)) (n := 12)
    (lo := (26657577 / 50000000)) (hi := (533151541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 586752877351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 586752877351) = 1/(586752877351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15265 : Bounds (-533151541 / 1000000000) (-26657577 / 50000000) (Real.log (586752877351 / 1000000000000)) := by
  have h := reflection_log_15265_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15266_neg : (763004047 / 500000000) ≤ -Real.log (50000000000 / 229988912439) ∧
    -Real.log (50000000000 / 229988912439) ≤ (1526008097 / 1000000000) := by
  have h := checkLog_sound (w := (29988912439 / 429988912439)) (n := 12)
    (lo := (69856867 / 500000000)) (hi := (27942747 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229988912439 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(229988912439 / 200000000000) = 1/(50000000000 / 229988912439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15266 : Bounds (763004047 / 500000000) (1526008097 / 1000000000) (Real.log (229988912439 / 50000000000)) := by
  have h := reflection_log_15266_neg
  have he : Real.log (229988912439 / 50000000000) = -Real.log (50000000000 / 229988912439) := by
    rw [show ((229988912439 / 50000000000) : ℝ) = ((50000000000 / 229988912439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15267_neg : (11946649 / 7812500) ≤ -Real.log (500000000000 / 2307175139657) ∧
    -Real.log (500000000000 / 2307175139657) ≤ (61166843 / 40000000) := by
  have h := checkLog_sound (w := (307175139657 / 4307175139657)) (n := 12)
    (lo := (17859589 / 125000000)) (hi := (142876713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2307175139657 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2307175139657 / 2000000000000) = 1/(500000000000 / 2307175139657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15267 : Bounds (11946649 / 7812500) (61166843 / 40000000) (Real.log (2307175139657 / 500000000000)) := by
  have h := reflection_log_15267_neg
  have he : Real.log (2307175139657 / 500000000000) = -Real.log (500000000000 / 2307175139657) := by
    rw [show ((2307175139657 / 500000000000) : ℝ) = ((500000000000 / 2307175139657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15268_neg : (5377088359 / 1000000000) ≤ -Real.log (500000000000 / 108195652173913) ∧
    -Real.log (500000000000 / 108195652173913) ≤ (5377088367 / 1000000000) := by
  have h := checkLog_sound (w := (44195652173913 / 172195652173913)) (n := 12)
    (lo := (525058099 / 1000000000)) (hi := (5250581 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108195652173913 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(108195652173913 / 64000000000000) = 1/(500000000000 / 108195652173913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15268 : Bounds (5377088359 / 1000000000) (5377088367 / 1000000000) (Real.log (108195652173913 / 500000000000)) := by
  have h := reflection_log_15268_neg
  have he : Real.log (108195652173913 / 500000000000) = -Real.log (500000000000 / 108195652173913) := by
    rw [show ((108195652173913 / 500000000000) : ℝ) = ((500000000000 / 108195652173913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15269_neg : (2699583861 / 500000000) ≤ -Real.log (62500000000 / 13826388888889) ∧
    -Real.log (62500000000 / 13826388888889) ≤ (539916773 / 100000000) := by
  have h := checkLog_sound (w := (5826388888889 / 21826388888889)) (n := 12)
    (lo := (273568731 / 500000000)) (hi := (547137463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13826388888889 / 8000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(13826388888889 / 8000000000000) = 1/(62500000000 / 13826388888889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15269 : Bounds (2699583861 / 500000000) (539916773 / 100000000) (Real.log (13826388888889 / 62500000000)) := by
  have h := reflection_log_15269_neg
  have he : Real.log (13826388888889 / 62500000000) = -Real.log (62500000000 / 13826388888889) := by
    rw [show ((13826388888889 / 62500000000) : ℝ) = ((62500000000 / 13826388888889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15270_neg : (10761523 / 15625000) ≤ -Real.log (1250 / 2489) ∧
    -Real.log (1250 / 2489) ≤ (688737473 / 1000000000) := by
  have h := checkLog_sound (w := (1239 / 3739)) (n := 12)
    (lo := (10761523 / 15625000)) (hi := (688737473 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2489 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2489 / 1250) = 1/(1250 / 2489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15270 : Bounds (10761523 / 15625000) (688737473 / 1000000000) (Real.log (2489 / 1250)) := by
  have h := reflection_log_15270_neg
  have he : Real.log (2489 / 1250) = -Real.log (1250 / 2489) := by
    rw [show ((2489 / 1250) : ℝ) = ((1250 / 2489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15271_neg : (2366501777 / 500000000) ≤ -Real.log (11 / 1250) ∧
    -Real.log (11 / 1250) ≤ (4733003561 / 1000000000) := by
  have h := checkLog_sound (w := (273 / 977)) (n := 12)
    (lo := (287060237 / 500000000)) (hi := (22964819 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 352) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(625 / 352) = 1/(11 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15271 : Bounds (-4733003561 / 1000000000) (-2366501777 / 500000000) (Real.log (11 / 1250)) := by
  have h := reflection_log_15271_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15272_neg : (990709 / 1000000000) ≤ -Real.log (1250000 / 1251239) ∧
    -Real.log (1250000 / 1251239) ≤ (99071 / 100000000) := by
  have h := checkLog_sound (w := (1239 / 2501239)) (n := 12)
    (lo := (990709 / 1000000000)) (hi := (99071 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251239 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251239 / 1250000) = 1/(1250000 / 1251239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15272 : Bounds (990709 / 1000000000) (99071 / 100000000) (Real.log (1251239 / 1250000)) := by
  have h := reflection_log_15272_neg
  have he : Real.log (1251239 / 1250000) = -Real.log (1250000 / 1251239) := by
    rw [show ((1251239 / 1250000) : ℝ) = ((1250000 / 1251239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15273_neg : (991691 / 1000000000) ≤ -Real.log (1248761 / 1250000) ∧
    -Real.log (1248761 / 1250000) ≤ (247923 / 250000000) := by
  have h := checkLog_sound (w := (1239 / 2498761)) (n := 12)
    (lo := (991691 / 1000000000)) (hi := (247923 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1248761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1248761) = 1/(1248761 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15273 : Bounds (-247923 / 250000000) (-991691 / 1000000000) (Real.log (1248761 / 1250000)) := by
  have h := reflection_log_15273_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15274_neg : (99321809 / 200000000) ≤ -Real.log (50000 / 82157) ∧
    -Real.log (50000 / 82157) ≤ (248304523 / 500000000) := by
  have h := checkLog_sound (w := (32157 / 132157)) (n := 12)
    (lo := (99321809 / 200000000)) (hi := (248304523 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82157 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82157 / 50000) = 1/(50000 / 82157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15274 : Bounds (99321809 / 200000000) (248304523 / 500000000) (Real.log (82157 / 50000)) := by
  have h := reflection_log_15274_neg
  have he : Real.log (82157 / 50000) = -Real.log (50000 / 82157) := by
    rw [show ((82157 / 50000) : ℝ) = ((50000 / 82157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15275_neg : (103041173 / 100000000) ≤ -Real.log (17843 / 50000) ∧
    -Real.log (17843 / 50000) ≤ (257602933 / 250000000) := by
  have h := checkLog_sound (w := (7157 / 42843)) (n := 12)
    (lo := (6745291 / 20000000)) (hi := (337264551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 17843) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(25000 / 17843) = 1/(17843 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15275 : Bounds (-257602933 / 250000000) (-103041173 / 100000000) (Real.log (17843 / 50000)) := by
  have h := reflection_log_15275_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15276_neg : (248586829 / 500000000) ≤ -Real.log (250000 / 411017) ∧
    -Real.log (250000 / 411017) ≤ (497173659 / 1000000000) := by
  have h := checkLog_sound (w := (161017 / 661017)) (n := 12)
    (lo := (248586829 / 500000000)) (hi := (497173659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((411017 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(411017 / 250000) = 1/(250000 / 411017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15276 : Bounds (248586829 / 500000000) (497173659 / 1000000000) (Real.log (411017 / 250000)) := by
  have h := reflection_log_15276_neg
  have he : Real.log (411017 / 250000) = -Real.log (250000 / 411017) := by
    rw [show ((411017 / 250000) : ℝ) = ((250000 / 411017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15277_neg : (1033015577 / 1000000000) ≤ -Real.log (88983 / 250000) ∧
    -Real.log (88983 / 250000) ≤ (1033015579 / 1000000000) := by
  have h := checkLog_sound (w := (36017 / 213983)) (n := 12)
    (lo := (339868397 / 1000000000)) (hi := (169934199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 88983) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 88983) = 1/(88983 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15277 : Bounds (-1033015579 / 1000000000) (-1033015577 / 1000000000) (Real.log (88983 / 250000)) := by
  have h := reflection_log_15277_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15278_neg : (535841919 / 1000000000) ≤ -Real.log (36573525711 / 62500000000) ∧
    -Real.log (36573525711 / 62500000000) ≤ (837253 / 1562500) := by
  have h := checkLog_sound (w := (25926474289 / 99073525711)) (n := 12)
    (lo := (535841919 / 1000000000)) (hi := (837253 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 36573525711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 36573525711) = 1/(36573525711 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15278 : Bounds (-837253 / 1562500) (-535841919 / 1000000000) (Real.log (36573525711 / 62500000000)) := by
  have h := reflection_log_15278_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15279_neg : (106760537 / 200000000) ≤ -Real.log (1465927351 / 2500000000) ∧
    -Real.log (1465927351 / 2500000000) ≤ (266901343 / 500000000) := by
  have h := checkLog_sound (w := (1034072649 / 3965927351)) (n := 12)
    (lo := (106760537 / 200000000)) (hi := (266901343 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 1465927351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 1465927351) = 1/(1465927351 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15279 : Bounds (-266901343 / 500000000) (-106760537 / 200000000) (Real.log (1465927351 / 2500000000)) := by
  have h := reflection_log_15279_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15280_neg : (61080831 / 40000000) ≤ -Real.log (500000000000 / 2302219357731) ∧
    -Real.log (500000000000 / 2302219357731) ≤ (763510389 / 500000000) := by
  have h := checkLog_sound (w := (302219357731 / 4302219357731)) (n := 12)
    (lo := (28145283 / 200000000)) (hi := (8795401 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2302219357731 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2302219357731 / 2000000000000) = 1/(500000000000 / 2302219357731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15280 : Bounds (61080831 / 40000000) (763510389 / 500000000) (Real.log (2302219357731 / 500000000000)) := by
  have h := reflection_log_15280_neg
  have he : Real.log (2302219357731 / 500000000000) = -Real.log (500000000000 / 2302219357731) := by
    rw [show ((2302219357731 / 500000000000) : ℝ) = ((500000000000 / 2302219357731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15281_neg : (765094617 / 500000000) ≤ -Real.log (500000000000 / 2309525414967) ∧
    -Real.log (500000000000 / 2309525414967) ≤ (1530189237 / 1000000000) := by
  have h := checkLog_sound (w := (309525414967 / 4309525414967)) (n := 12)
    (lo := (71947437 / 500000000)) (hi := (1151159 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2309525414967 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2309525414967 / 2000000000000) = 1/(500000000000 / 2309525414967) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15281 : Bounds (765094617 / 500000000) (1530189237 / 1000000000) (Real.log (2309525414967 / 500000000000)) := by
  have h := reflection_log_15281_neg
  have he : Real.log (2309525414967 / 500000000000) = -Real.log (500000000000 / 2309525414967) := by
    rw [show ((2309525414967 / 500000000000) : ℝ) = ((500000000000 / 2309525414967) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15282_neg : (2699583861 / 500000000) ≤ -Real.log (500000000000 / 110611111111111) ∧
    -Real.log (500000000000 / 110611111111111) ≤ (539916773 / 100000000) := by
  have h := checkLog_sound (w := (46611111111111 / 174611111111111)) (n := 12)
    (lo := (273568731 / 500000000)) (hi := (547137463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((110611111111111 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(110611111111111 / 64000000000000) = 1/(500000000000 / 110611111111111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15282 : Bounds (2699583861 / 500000000) (539916773 / 100000000) (Real.log (110611111111111 / 500000000000)) := by
  have h := reflection_log_15282_neg
  have he : Real.log (110611111111111 / 500000000000) = -Real.log (500000000000 / 110611111111111) := by
    rw [show ((110611111111111 / 500000000000) : ℝ) = ((500000000000 / 110611111111111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15283_neg : (216869641 / 40000000) ≤ -Real.log (125000000000 / 28284090909091) ∧
    -Real.log (125000000000 / 28284090909091) ≤ (5421741033 / 1000000000) := by
  have h := checkLog_sound (w := (12284090909091 / 44284090909091)) (n := 12)
    (lo := (113942153 / 200000000)) (hi := (284855383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28284090909091 / 16000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(28284090909091 / 16000000000000) = 1/(125000000000 / 28284090909091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15283 : Bounds (216869641 / 40000000) (5421741033 / 1000000000) (Real.log (28284090909091 / 125000000000)) := by
  have h := reflection_log_15283_neg
  have he : Real.log (28284090909091 / 125000000000) = -Real.log (125000000000 / 28284090909091) := by
    rw [show ((28284090909091 / 125000000000) : ℝ) = ((125000000000 / 28284090909091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15284_neg : (172209477 / 250000000) ≤ -Real.log (5000 / 9957) ∧
    -Real.log (5000 / 9957) ≤ (688837909 / 1000000000) := by
  have h := checkLog_sound (w := (4957 / 14957)) (n := 12)
    (lo := (172209477 / 250000000)) (hi := (688837909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9957 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9957 / 5000) = 1/(5000 / 9957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15284 : Bounds (172209477 / 250000000) (688837909 / 1000000000) (Real.log (9957 / 5000)) := by
  have h := reflection_log_15284_neg
  have he : Real.log (9957 / 5000) = -Real.log (5000 / 9957) := by
    rw [show ((9957 / 5000) : ℝ) = ((5000 / 9957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15285_neg : (297249567 / 62500000) ≤ -Real.log (43 / 5000) ∧
    -Real.log (43 / 5000) ≤ (4755993079 / 1000000000) := by
  have h := checkLog_sound (w := (281 / 969)) (n := 12)
    (lo := (74638749 / 125000000)) (hi := (597109993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 344) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(625 / 344) = 1/(43 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15285 : Bounds (-4755993079 / 1000000000) (-297249567 / 62500000) (Real.log (43 / 5000)) := by
  have h := reflection_log_15285_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15286_neg : (247727 / 250000000) ≤ -Real.log (5000000 / 5004957) ∧
    -Real.log (5000000 / 5004957) ≤ (990909 / 1000000000) := by
  have h := checkLog_sound (w := (4957 / 10004957)) (n := 12)
    (lo := (247727 / 250000000)) (hi := (990909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004957 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004957 / 5000000) = 1/(5000000 / 5004957) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15286 : Bounds (247727 / 250000000) (990909 / 1000000000) (Real.log (5004957 / 5000000)) := by
  have h := reflection_log_15286_neg
  have he : Real.log (5004957 / 5000000) = -Real.log (5000000 / 5004957) := by
    rw [show ((5004957 / 5000000) : ℝ) = ((5000000 / 5004957) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15287_neg : (991891 / 1000000000) ≤ -Real.log (4995043 / 5000000) ∧
    -Real.log (4995043 / 5000000) ≤ (247973 / 250000000) := by
  have h := checkLog_sound (w := (4957 / 9995043)) (n := 12)
    (lo := (991891 / 1000000000)) (hi := (247973 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995043) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995043) = 1/(4995043 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15287 : Bounds (-247973 / 250000000) (-991891 / 1000000000) (Real.log (4995043 / 5000000)) := by
  have h := reflection_log_15287_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15288_neg : (496790997 / 1000000000) ≤ -Real.log (1000000 / 1643439) ∧
    -Real.log (1000000 / 1643439) ≤ (248395499 / 500000000) := by
  have h := checkLog_sound (w := (643439 / 2643439)) (n := 12)
    (lo := (496790997 / 1000000000)) (hi := (248395499 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1643439 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1643439 / 1000000) = 1/(1000000 / 1643439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15288 : Bounds (496790997 / 1000000000) (248395499 / 500000000) (Real.log (1643439 / 1000000)) := by
  have h := reflection_log_15288_neg
  have he : Real.log (1643439 / 1000000) = -Real.log (1000000 / 1643439) := by
    rw [show ((1643439 / 1000000) : ℝ) = ((1000000 / 1643439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15289_neg : (206249989 / 200000000) ≤ -Real.log (356561 / 1000000) ∧
    -Real.log (356561 / 1000000) ≤ (1031249947 / 1000000000) := by
  have h := checkLog_sound (w := (143439 / 856561)) (n := 12)
    (lo := (67620553 / 200000000)) (hi := (169051383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 356561) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 356561) = 1/(356561 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15289 : Bounds (-1031249947 / 1000000000) (-206249989 / 200000000) (Real.log (356561 / 1000000)) := by
  have h := reflection_log_15289_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15290_neg : (99471223 / 200000000) ≤ -Real.log (62500 / 102773) ∧
    -Real.log (62500 / 102773) ≤ (124339029 / 250000000) := by
  have h := checkLog_sound (w := (40273 / 165273)) (n := 12)
    (lo := (99471223 / 200000000)) (hi := (124339029 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102773 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(102773 / 62500) = 1/(62500 / 102773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15290 : Bounds (99471223 / 200000000) (124339029 / 250000000) (Real.log (102773 / 62500)) := by
  have h := reflection_log_15290_neg
  have he : Real.log (102773 / 62500) = -Real.log (62500 / 102773) := by
    rw [show ((102773 / 62500) : ℝ) = ((62500 / 102773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15291_neg : (103385879 / 100000000) ≤ -Real.log (22227 / 62500) ∧
    -Real.log (22227 / 62500) ≤ (129232349 / 125000000) := by
  have h := checkLog_sound (w := (9023 / 53477)) (n := 12)
    (lo := (34071161 / 100000000)) (hi := (340711611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 22227) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 22227) = 1/(22227 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15291 : Bounds (-129232349 / 125000000) (-103385879 / 100000000) (Real.log (22227 / 62500)) := by
  have h := reflection_log_15291_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15292_neg : (268251337 / 500000000) ≤ -Real.log (2284335471 / 3906250000) ∧
    -Real.log (2284335471 / 3906250000) ≤ (21460107 / 40000000) := by
  have h := checkLog_sound (w := (1621914529 / 6190585471)) (n := 12)
    (lo := (268251337 / 500000000)) (hi := (21460107 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 2284335471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 2284335471) = 1/(2284335471 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15292 : Bounds (-21460107 / 40000000) (-268251337 / 500000000) (Real.log (2284335471 / 3906250000)) := by
  have h := reflection_log_15292_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15293_neg : (133614737 / 250000000) ≤ -Real.log (585986253279 / 1000000000000) ∧
    -Real.log (585986253279 / 1000000000000) ≤ (534458949 / 1000000000) := by
  have h := checkLog_sound (w := (414013746721 / 1585986253279)) (n := 12)
    (lo := (133614737 / 250000000)) (hi := (534458949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 585986253279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 585986253279) = 1/(585986253279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15293 : Bounds (-534458949 / 1000000000) (-133614737 / 250000000) (Real.log (585986253279 / 1000000000000)) := by
  have h := reflection_log_15293_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15294_neg : (764020471 / 500000000) ≤ -Real.log (500000000000 / 2304569204147) ∧
    -Real.log (500000000000 / 2304569204147) ≤ (305608189 / 200000000) := by
  have h := checkLog_sound (w := (304569204147 / 4304569204147)) (n := 12)
    (lo := (70873291 / 500000000)) (hi := (141746583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2304569204147 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2304569204147 / 2000000000000) = 1/(500000000000 / 2304569204147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15294 : Bounds (764020471 / 500000000) (305608189 / 200000000) (Real.log (2304569204147 / 500000000000)) := by
  have h := reflection_log_15294_neg
  have he : Real.log (2304569204147 / 500000000000) = -Real.log (500000000000 / 2304569204147) := by
    rw [show ((2304569204147 / 500000000000) : ℝ) = ((500000000000 / 2304569204147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15295_neg : (306242981 / 200000000) ≤ -Real.log (6250000000 / 28898693031) ∧
    -Real.log (6250000000 / 28898693031) ≤ (382803727 / 250000000) := by
  have h := checkLog_sound (w := (3898693031 / 53898693031)) (n := 12)
    (lo := (28984109 / 200000000)) (hi := (72460273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28898693031 / 25000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(28898693031 / 25000000000) = 1/(6250000000 / 28898693031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15295 : Bounds (306242981 / 200000000) (382803727 / 250000000) (Real.log (28898693031 / 6250000000)) := by
  have h := reflection_log_15295_neg
  have he : Real.log (28898693031 / 6250000000) = -Real.log (6250000000 / 28898693031) := by
    rw [show ((28898693031 / 6250000000) : ℝ) = ((6250000000 / 28898693031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
