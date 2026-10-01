import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0026
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

theorem reflection_log_1_neg : (12302411 / 31250000) ≤ -Real.log (512 / 759) ∧
    -Real.log (512 / 759) ≤ (393677153 / 1000000000) := by
  have h := checkLog_sound (w := (247 / 1271)) (n := 12)
    (lo := (12302411 / 31250000)) (hi := (393677153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((759 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(759 / 512) = 1/(512 / 759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (12302411 / 31250000) (393677153 / 1000000000) (Real.log (759 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (759 / 512) = -Real.log (512 / 759) := by
    rw [show ((759 / 512) : ℝ) = ((512 / 759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (658594799 / 1000000000) ≤ -Real.log (265 / 512) ∧
    -Real.log (265 / 512) ≤ (1646487 / 2500000) := by
  have h := checkLog_sound (w := (247 / 777)) (n := 12)
    (lo := (658594799 / 1000000000)) (hi := (1646487 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 265) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 265) = 1/(265 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1646487 / 2500000) (-658594799 / 1000000000) (Real.log (265 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (15715453 / 40000000) ≤ -Real.log (160 / 237) ∧
    -Real.log (160 / 237) ≤ (196443163 / 500000000) := by
  have h := checkLog_sound (w := (77 / 397)) (n := 12)
    (lo := (15715453 / 40000000)) (hi := (196443163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((237 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(237 / 160) = 1/(160 / 237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (15715453 / 40000000) (196443163 / 500000000) (Real.log (237 / 160)) := by
  have h := reflection_log_3_neg
  have he : Real.log (237 / 160) = -Real.log (160 / 237) := by
    rw [show ((237 / 160) : ℝ) = ((160 / 237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (656333207 / 1000000000) ≤ -Real.log (83 / 160) ∧
    -Real.log (83 / 160) ≤ (82041651 / 125000000) := by
  have h := checkLog_sound (w := (77 / 243)) (n := 12)
    (lo := (656333207 / 1000000000)) (hi := (82041651 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 83) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160 / 83) = 1/(83 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-82041651 / 125000000) (-656333207 / 1000000000) (Real.log (83 / 160)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (27016509 / 40000000) ≤ -Real.log (256 / 503) ∧
    -Real.log (256 / 503) ≤ (337706363 / 500000000) := by
  have h := checkLog_sound (w := (247 / 759)) (n := 12)
    (lo := (27016509 / 40000000)) (hi := (337706363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((503 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(503 / 256) = 1/(256 / 503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (27016509 / 40000000) (337706363 / 500000000) (Real.log (503 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (503 / 256) = -Real.log (256 / 503) := by
    rw [show ((503 / 256) : ℝ) = ((256 / 503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (104623527 / 31250000) ≤ -Real.log (9 / 256) ∧
    -Real.log (9 / 256) ≤ (3347952869 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(16 / 9) = 1/(9 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-3347952869 / 1000000000) (-104623527 / 31250000) (Real.log (9 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (67421917 / 100000000) ≤ -Real.log (80 / 157) ∧
    -Real.log (80 / 157) ≤ (674219171 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 237)) (n := 12)
    (lo := (67421917 / 100000000)) (hi := (674219171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157 / 80) = 1/(80 / 157) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (67421917 / 100000000) (674219171 / 1000000000) (Real.log (157 / 80)) := by
  have h := reflection_log_7_neg
  have he : Real.log (157 / 80) = -Real.log (80 / 157) := by
    rw [show ((157 / 80) : ℝ) = ((80 / 157) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (3283414343 / 1000000000) ≤ -Real.log (3 / 80) ∧
    -Real.log (3 / 80) ≤ (820853587 / 250000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(5 / 3) = 1/(3 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-820853587 / 250000000) (-3283414343 / 1000000000) (Real.log (3 / 80)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (109951759 / 200000000) ≤ -Real.log (200000 / 346567) ∧
    -Real.log (200000 / 346567) ≤ (137439699 / 250000000) := by
  have h := checkLog_sound (w := (146567 / 546567)) (n := 12)
    (lo := (109951759 / 200000000)) (hi := (137439699 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((346567 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(346567 / 200000) = 1/(200000 / 346567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (109951759 / 200000000) (137439699 / 250000000) (Real.log (346567 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (346567 / 200000) = -Real.log (200000 / 346567) := by
    rw [show ((346567 / 200000) : ℝ) = ((200000 / 346567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1319888833 / 1000000000) ≤ -Real.log (53433 / 200000) ∧
    -Real.log (53433 / 200000) ≤ (263977767 / 200000000) := by
  have h := checkLog_sound (w := (46567 / 153433)) (n := 12)
    (lo := (626741653 / 1000000000)) (hi := (313370827 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 53433) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 53433) = 1/(53433 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-263977767 / 200000000) (-1319888833 / 1000000000) (Real.log (53433 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (551197597 / 1000000000) ≤ -Real.log (100000 / 173533) ∧
    -Real.log (100000 / 173533) ≤ (275598799 / 500000000) := by
  have h := checkLog_sound (w := (73533 / 273533)) (n := 12)
    (lo := (551197597 / 1000000000)) (hi := (275598799 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173533 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173533 / 100000) = 1/(100000 / 173533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (551197597 / 1000000000) (275598799 / 500000000) (Real.log (173533 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (173533 / 100000) = -Real.log (100000 / 173533) := by
    rw [show ((173533 / 100000) : ℝ) = ((100000 / 173533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1329271511 / 1000000000) ≤ -Real.log (26467 / 100000) ∧
    -Real.log (26467 / 100000) ≤ (1329271513 / 1000000000) := by
  have h := checkLog_sound (w := (23533 / 76467)) (n := 12)
    (lo := (636124331 / 1000000000)) (hi := (159031083 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 26467) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 26467) = 1/(26467 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1329271513 / 1000000000) (-1329271511 / 1000000000) (Real.log (26467 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (474223463 / 1000000000) ≤ -Real.log (500000 / 803383) ∧
    -Real.log (500000 / 803383) ≤ (59277933 / 125000000) := by
  have h := checkLog_sound (w := (303383 / 1303383)) (n := 12)
    (lo := (474223463 / 1000000000)) (hi := (59277933 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((803383 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(803383 / 500000) = 1/(500000 / 803383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (474223463 / 1000000000) (59277933 / 125000000) (Real.log (803383 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (803383 / 500000) = -Real.log (500000 / 803383) := by
    rw [show ((803383 / 500000) : ℝ) = ((500000 / 803383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (933350423 / 1000000000) ≤ -Real.log (196617 / 500000) ∧
    -Real.log (196617 / 500000) ≤ (37334017 / 40000000) := by
  have h := checkLog_sound (w := (53383 / 446617)) (n := 12)
    (lo := (240203243 / 1000000000)) (hi := (60050811 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 196617) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 196617) = 1/(196617 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-37334017 / 40000000) (-933350423 / 1000000000) (Real.log (196617 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (475924193 / 1000000000) ≤ -Real.log (1000000 / 1609501) ∧
    -Real.log (1000000 / 1609501) ≤ (237962097 / 500000000) := by
  have h := checkLog_sound (w := (609501 / 2609501)) (n := 12)
    (lo := (475924193 / 1000000000)) (hi := (237962097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1609501 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1609501 / 1000000) = 1/(1000000 / 1609501) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (475924193 / 1000000000) (237962097 / 500000000) (Real.log (1609501 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1609501 / 1000000) = -Real.log (1000000 / 1609501) := by
    rw [show ((1609501 / 1000000) : ℝ) = ((1000000 / 1609501) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (940329869 / 1000000000) ≤ -Real.log (390499 / 1000000) ∧
    -Real.log (390499 / 1000000) ≤ (940329871 / 1000000000) := by
  have h := checkLog_sound (w := (109501 / 890499)) (n := 12)
    (lo := (247182689 / 1000000000)) (hi := (24718269 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 390499) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 390499) = 1/(390499 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-940329871 / 1000000000) (-940329869 / 1000000000) (Real.log (390499 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (467411907 / 250000000) ≤ -Real.log (250000000000 / 1621502629461) ∧
    -Real.log (250000000000 / 1621502629461) ≤ (1869647631 / 1000000000) := by
  have h := checkLog_sound (w := (621502629461 / 2621502629461)) (n := 12)
    (lo := (120838317 / 250000000)) (hi := (483353269 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1621502629461 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1621502629461 / 1000000000000) = 1/(250000000000 / 1621502629461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (467411907 / 250000000) (1869647631 / 1000000000) (Real.log (1621502629461 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1621502629461 / 250000000000) = -Real.log (250000000000 / 1621502629461) := by
    rw [show ((1621502629461 / 250000000000) : ℝ) = ((250000000000 / 1621502629461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1880469107 / 1000000000) ≤ -Real.log (500000000000 / 3278289945971) ∧
    -Real.log (500000000000 / 3278289945971) ≤ (188046911 / 100000000) := by
  have h := checkLog_sound (w := (1278289945971 / 5278289945971)) (n := 12)
    (lo := (494174747 / 1000000000)) (hi := (123543687 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3278289945971 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3278289945971 / 2000000000000) = 1/(500000000000 / 3278289945971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1880469107 / 1000000000) (188046911 / 100000000) (Real.log (3278289945971 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (3278289945971 / 500000000000) = -Real.log (500000000000 / 3278289945971) := by
    rw [show ((3278289945971 / 500000000000) : ℝ) = ((500000000000 / 3278289945971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (703786943 / 500000000) ≤ -Real.log (500000000000 / 2043015100423) ∧
    -Real.log (500000000000 / 2043015100423) ≤ (1407573889 / 1000000000) := by
  have h := checkLog_sound (w := (43015100423 / 4043015100423)) (n := 12)
    (lo := (10639763 / 500000000)) (hi := (21279527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2043015100423 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2043015100423 / 2000000000000) = 1/(500000000000 / 2043015100423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (703786943 / 500000000) (1407573889 / 1000000000) (Real.log (2043015100423 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2043015100423 / 500000000000) = -Real.log (500000000000 / 2043015100423) := by
    rw [show ((2043015100423 / 500000000000) : ℝ) = ((500000000000 / 2043015100423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (708127031 / 500000000) ≤ -Real.log (250000000000 / 1030413010021) ∧
    -Real.log (250000000000 / 1030413010021) ≤ (283250813 / 200000000) := by
  have h := checkLog_sound (w := (30413010021 / 2030413010021)) (n := 12)
    (lo := (14979851 / 500000000)) (hi := (29959703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1030413010021 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1030413010021 / 1000000000000) = 1/(250000000000 / 1030413010021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (708127031 / 500000000) (283250813 / 200000000) (Real.log (1030413010021 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1030413010021 / 250000000000) = -Real.log (250000000000 / 1030413010021) := by
    rw [show ((1030413010021 / 250000000000) : ℝ) = ((250000000000 / 1030413010021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0026
