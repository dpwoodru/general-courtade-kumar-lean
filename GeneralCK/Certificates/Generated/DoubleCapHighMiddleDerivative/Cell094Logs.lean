import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell094
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (266711771 / 1000000000) ≤ -Real.log (1024 / 1337) ∧
    -Real.log (1024 / 1337) ≤ (66677943 / 250000000) := by
  have h := checkLog_sound (w := (313 / 2361)) (n := 12)
    (lo := (266711771 / 1000000000)) (hi := (66677943 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1337 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1337 / 1024) = 1/(1024 / 1337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (266711771 / 1000000000) (66677943 / 250000000) (Real.log (1337 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1337 / 1024) = -Real.log (1024 / 1337) := by
    rw [show ((1337 / 1024) : ℝ) = ((1024 / 1337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (583679 / 1600000) ≤ -Real.log (711 / 1024) ∧
    -Real.log (711 / 1024) ≤ (22799961 / 62500000) := by
  have h := checkLog_sound (w := (313 / 1735)) (n := 12)
    (lo := (583679 / 1600000)) (hi := (22799961 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 711) = 1/(711 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-22799961 / 62500000) (-583679 / 1600000) (Real.log (711 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (33282863 / 125000000) ≤ -Real.log (2560 / 3341) ∧
    -Real.log (2560 / 3341) ≤ (53252581 / 200000000) := by
  have h := checkLog_sound (w := (781 / 5901)) (n := 12)
    (lo := (33282863 / 125000000)) (hi := (53252581 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3341 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3341 / 2560) = 1/(2560 / 3341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (33282863 / 125000000) (53252581 / 200000000) (Real.log (3341 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3341 / 2560) = -Real.log (2560 / 3341) := by
    rw [show ((3341 / 2560) : ℝ) = ((2560 / 3341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (363955849 / 1000000000) ≤ -Real.log (1779 / 2560) ∧
    -Real.log (1779 / 2560) ≤ (7279117 / 20000000) := by
  have h := checkLog_sound (w := (781 / 4339)) (n := 12)
    (lo := (363955849 / 1000000000)) (hi := (7279117 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1779) = 1/(1779 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-7279117 / 20000000) (-363955849 / 1000000000) (Real.log (1779 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (196053507 / 1000000000) ≤ -Real.log (62500 / 76037) ∧
    -Real.log (62500 / 76037) ≤ (49013377 / 250000000) := by
  have h := checkLog_sound (w := (13537 / 138537)) (n := 12)
    (lo := (196053507 / 1000000000)) (hi := (49013377 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76037 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(76037 / 62500) = 1/(62500 / 76037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (196053507 / 1000000000) (49013377 / 250000000) (Real.log (76037 / 62500)) := by
  have h := reflection_log_5_neg
  have he : Real.log (76037 / 62500) = -Real.log (62500 / 76037) := by
    rw [show ((76037 / 62500) : ℝ) = ((62500 / 76037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (48820329 / 200000000) ≤ -Real.log (48963 / 62500) ∧
    -Real.log (48963 / 62500) ≤ (122050823 / 500000000) := by
  have h := checkLog_sound (w := (13537 / 111463)) (n := 12)
    (lo := (48820329 / 200000000)) (hi := (122050823 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 48963) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 48963) = 1/(48963 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-122050823 / 500000000) (-48820329 / 200000000) (Real.log (48963 / 62500)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (39279899 / 200000000) ≤ -Real.log (1000000 / 1217013) ∧
    -Real.log (1000000 / 1217013) ≤ (24549937 / 125000000) := by
  have h := checkLog_sound (w := (217013 / 2217013)) (n := 12)
    (lo := (39279899 / 200000000)) (hi := (24549937 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1217013 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1217013 / 1000000) = 1/(1000000 / 1217013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (39279899 / 200000000) (24549937 / 125000000) (Real.log (1217013 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1217013 / 1000000) = -Real.log (1000000 / 1217013) := by
    rw [show ((1217013 / 1000000) : ℝ) = ((1000000 / 1217013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (48927837 / 200000000) ≤ -Real.log (782987 / 1000000) ∧
    -Real.log (782987 / 1000000) ≤ (122319593 / 500000000) := by
  have h := checkLog_sound (w := (217013 / 1782987)) (n := 12)
    (lo := (48927837 / 200000000)) (hi := (122319593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 782987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 782987) = 1/(782987 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-122319593 / 500000000) (-48927837 / 200000000) (Real.log (782987 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (2253881 / 15625000) ≤ -Real.log (1000000 / 1155171) ∧
    -Real.log (1000000 / 1155171) ≤ (28849677 / 200000000) := by
  have h := checkLog_sound (w := (155171 / 2155171)) (n := 12)
    (lo := (2253881 / 15625000)) (hi := (28849677 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1155171 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1155171 / 1000000) = 1/(1000000 / 1155171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (2253881 / 15625000) (28849677 / 200000000) (Real.log (1155171 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1155171 / 1000000) = -Real.log (1000000 / 1155171) := by
    rw [show ((1155171 / 1000000) : ℝ) = ((1000000 / 1155171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (84310519 / 500000000) ≤ -Real.log (844829 / 1000000) ∧
    -Real.log (844829 / 1000000) ≤ (168621039 / 1000000000) := by
  have h := checkLog_sound (w := (155171 / 1844829)) (n := 12)
    (lo := (84310519 / 500000000)) (hi := (168621039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 844829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 844829) = 1/(844829 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-168621039 / 1000000000) (-84310519 / 500000000) (Real.log (844829 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (144516707 / 1000000000) ≤ -Real.log (1000000 / 1155481) ∧
    -Real.log (1000000 / 1155481) ≤ (36129177 / 250000000) := by
  have h := checkLog_sound (w := (155481 / 2155481)) (n := 12)
    (lo := (144516707 / 1000000000)) (hi := (36129177 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1155481 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1155481 / 1000000) = 1/(1000000 / 1155481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (144516707 / 1000000000) (36129177 / 250000000) (Real.log (1155481 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1155481 / 1000000) = -Real.log (1000000 / 1155481) := by
    rw [show ((1155481 / 1000000) : ℝ) = ((1000000 / 1155481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (42247011 / 250000000) ≤ -Real.log (844519 / 1000000) ∧
    -Real.log (844519 / 1000000) ≤ (33797609 / 200000000) := by
  have h := checkLog_sound (w := (155481 / 1844519)) (n := 12)
    (lo := (42247011 / 250000000)) (hi := (33797609 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 844519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 844519) = 1/(844519 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-33797609 / 200000000) (-42247011 / 250000000) (Real.log (844519 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (315109377 / 500000000) ≤ -Real.log (500000000000 / 939010680157) ∧
    -Real.log (500000000000 / 939010680157) ≤ (126043751 / 200000000) := by
  have h := checkLog_sound (w := (439010680157 / 1439010680157)) (n := 12)
    (lo := (315109377 / 500000000)) (hi := (126043751 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((939010680157 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(939010680157 / 500000000000) = 1/(500000000000 / 939010680157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (315109377 / 500000000) (126043751 / 200000000) (Real.log (939010680157 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (939010680157 / 500000000000) = -Real.log (500000000000 / 939010680157) := by
    rw [show ((939010680157 / 500000000000) : ℝ) = ((500000000000 / 939010680157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (631511147 / 1000000000) ≤ -Real.log (250000000000 / 470112517581) ∧
    -Real.log (250000000000 / 470112517581) ≤ (157877787 / 250000000) := by
  have h := checkLog_sound (w := (220112517581 / 720112517581)) (n := 12)
    (lo := (631511147 / 1000000000)) (hi := (157877787 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((470112517581 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(470112517581 / 250000000000) = 1/(250000000000 / 470112517581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (631511147 / 1000000000) (157877787 / 250000000) (Real.log (470112517581 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (470112517581 / 250000000000) = -Real.log (250000000000 / 470112517581) := by
    rw [show ((470112517581 / 250000000000) : ℝ) = ((250000000000 / 470112517581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (440155153 / 1000000000) ≤ -Real.log (250000000000 / 388237036129) ∧
    -Real.log (250000000000 / 388237036129) ≤ (220077577 / 500000000) := by
  have h := checkLog_sound (w := (138237036129 / 638237036129)) (n := 12)
    (lo := (440155153 / 1000000000)) (hi := (220077577 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((388237036129 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(388237036129 / 250000000000) = 1/(250000000000 / 388237036129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (440155153 / 1000000000) (220077577 / 500000000) (Real.log (388237036129 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (388237036129 / 250000000000) = -Real.log (250000000000 / 388237036129) := by
    rw [show ((388237036129 / 250000000000) : ℝ) = ((250000000000 / 388237036129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (441038681 / 1000000000) ≤ -Real.log (4000000000 / 6217283301) ∧
    -Real.log (4000000000 / 6217283301) ≤ (220519341 / 500000000) := by
  have h := checkLog_sound (w := (2217283301 / 10217283301)) (n := 12)
    (lo := (441038681 / 1000000000)) (hi := (220519341 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6217283301 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6217283301 / 4000000000) = 1/(4000000000 / 6217283301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (441038681 / 1000000000) (220519341 / 500000000) (Real.log (6217283301 / 4000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (6217283301 / 4000000000) = -Real.log (4000000000 / 6217283301) := by
    rw [show ((6217283301 / 4000000000) : ℝ) = ((4000000000 / 6217283301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (312869423 / 1000000000) ≤ -Real.log (500000000000 / 683671488549) ∧
    -Real.log (500000000000 / 683671488549) ≤ (19554339 / 62500000) := by
  have h := checkLog_sound (w := (183671488549 / 1183671488549)) (n := 12)
    (lo := (312869423 / 1000000000)) (hi := (19554339 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((683671488549 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(683671488549 / 500000000000) = 1/(500000000000 / 683671488549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (312869423 / 1000000000) (19554339 / 62500000) (Real.log (683671488549 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (683671488549 / 500000000000) = -Real.log (500000000000 / 683671488549) := by
    rw [show ((683671488549 / 500000000000) : ℝ) = ((500000000000 / 683671488549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (313504751 / 1000000000) ≤ -Real.log (250000000000 / 342052991111) ∧
    -Real.log (250000000000 / 342052991111) ≤ (19594047 / 62500000) := by
  have h := checkLog_sound (w := (92052991111 / 592052991111)) (n := 12)
    (lo := (313504751 / 1000000000)) (hi := (19594047 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342052991111 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342052991111 / 250000000000) = 1/(250000000000 / 342052991111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (313504751 / 1000000000) (19594047 / 62500000) (Real.log (342052991111 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (342052991111 / 250000000000) = -Real.log (250000000000 / 342052991111) := by
    rw [show ((342052991111 / 250000000000) : ℝ) = ((250000000000 / 342052991111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3058917 / 125000000) ≤ -Real.log (975825658639 / 1000000000000) ∧
    -Real.log (975825658639 / 1000000000000) ≤ (24471337 / 1000000000) := by
  have h := checkLog_sound (w := (24174341361 / 1975825658639)) (n := 12)
    (lo := (3058917 / 125000000)) (hi := (24471337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975825658639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975825658639) = 1/(975825658639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-24471337 / 1000000000) (-3058917 / 125000000) (Real.log (975825658639 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (12186327 / 500000000) ≤ -Real.log (975921960759 / 1000000000000) ∧
    -Real.log (975921960759 / 1000000000000) ≤ (4874531 / 200000000) := by
  have h := checkLog_sound (w := (24078039241 / 1975921960759)) (n := 12)
    (lo := (12186327 / 500000000)) (hi := (4874531 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 975921960759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 975921960759) = 1/(975921960759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-4874531 / 200000000) (-12186327 / 500000000) (Real.log (975921960759 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell094
