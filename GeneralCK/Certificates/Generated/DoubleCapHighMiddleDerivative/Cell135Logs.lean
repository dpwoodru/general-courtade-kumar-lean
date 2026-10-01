import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell135
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

theorem reflection_log_1_neg : (17808997 / 62500000) ≤ -Real.log (640 / 851) ∧
    -Real.log (640 / 851) ≤ (284943953 / 1000000000) := by
  have h := checkLog_sound (w := (211 / 1491)) (n := 12)
    (lo := (17808997 / 62500000)) (hi := (284943953 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851 / 640) = 1/(640 / 851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (17808997 / 62500000) (284943953 / 1000000000) (Real.log (851 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (851 / 640) = -Real.log (640 / 851) := by
    rw [show ((851 / 640) : ℝ) = ((640 / 851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (400011257 / 1000000000) ≤ -Real.log (429 / 640) ∧
    -Real.log (429 / 640) ≤ (200005629 / 500000000) := by
  have h := checkLog_sound (w := (211 / 1069)) (n := 12)
    (lo := (400011257 / 1000000000)) (hi := (200005629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 429) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 429) = 1/(429 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-200005629 / 500000000) (-400011257 / 1000000000) (Real.log (429 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (284503197 / 1000000000) ≤ -Real.log (1024 / 1361) ∧
    -Real.log (1024 / 1361) ≤ (142251599 / 500000000) := by
  have h := checkLog_sound (w := (337 / 2385)) (n := 12)
    (lo := (284503197 / 1000000000)) (hi := (142251599 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1361 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1361 / 1024) = 1/(1024 / 1361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (284503197 / 1000000000) (142251599 / 500000000) (Real.log (1361 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1361 / 1024) = -Real.log (1024 / 1361) := by
    rw [show ((1361 / 1024) : ℝ) = ((1024 / 1361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (399137513 / 1000000000) ≤ -Real.log (687 / 1024) ∧
    -Real.log (687 / 1024) ≤ (199568757 / 500000000) := by
  have h := checkLog_sound (w := (337 / 1711)) (n := 12)
    (lo := (399137513 / 1000000000)) (hi := (199568757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 687) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 687) = 1/(687 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-199568757 / 500000000) (-399137513 / 1000000000) (Real.log (687 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (52526533 / 250000000) ≤ -Real.log (1000000 / 1233809) ∧
    -Real.log (1000000 / 1233809) ≤ (210106133 / 1000000000) := by
  have h := checkLog_sound (w := (233809 / 2233809)) (n := 12)
    (lo := (52526533 / 250000000)) (hi := (210106133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1233809 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1233809 / 1000000) = 1/(1000000 / 1233809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (52526533 / 250000000) (210106133 / 1000000000) (Real.log (1233809 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1233809 / 1000000) = -Real.log (1000000 / 1233809) := by
    rw [show ((1233809 / 1000000) : ℝ) = ((1000000 / 1233809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (266323793 / 1000000000) ≤ -Real.log (766191 / 1000000) ∧
    -Real.log (766191 / 1000000) ≤ (133161897 / 500000000) := by
  have h := checkLog_sound (w := (233809 / 1766191)) (n := 12)
    (lo := (266323793 / 1000000000)) (hi := (133161897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 766191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 766191) = 1/(766191 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-133161897 / 500000000) (-266323793 / 1000000000) (Real.log (766191 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (26306013 / 125000000) ≤ -Real.log (1000000 / 1234231) ∧
    -Real.log (1000000 / 1234231) ≤ (42089621 / 200000000) := by
  have h := checkLog_sound (w := (234231 / 2234231)) (n := 12)
    (lo := (26306013 / 125000000)) (hi := (42089621 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1234231 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1234231 / 1000000) = 1/(1000000 / 1234231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (26306013 / 125000000) (42089621 / 200000000) (Real.log (1234231 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1234231 / 1000000) = -Real.log (1000000 / 1234231) := by
    rw [show ((1234231 / 1000000) : ℝ) = ((1000000 / 1234231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (266874721 / 1000000000) ≤ -Real.log (765769 / 1000000) ∧
    -Real.log (765769 / 1000000) ≤ (133437361 / 500000000) := by
  have h := checkLog_sound (w := (234231 / 1765769)) (n := 12)
    (lo := (266874721 / 1000000000)) (hi := (133437361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 765769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 765769) = 1/(765769 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-133437361 / 500000000) (-266874721 / 1000000000) (Real.log (765769 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (155182433 / 1000000000) ≤ -Real.log (1000000 / 1167871) ∧
    -Real.log (1000000 / 1167871) ≤ (77591217 / 500000000) := by
  have h := checkLog_sound (w := (167871 / 2167871)) (n := 12)
    (lo := (155182433 / 1000000000)) (hi := (77591217 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1167871 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1167871 / 1000000) = 1/(1000000 / 1167871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (155182433 / 1000000000) (77591217 / 500000000) (Real.log (1167871 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1167871 / 1000000) = -Real.log (1000000 / 1167871) := by
    rw [show ((1167871 / 1000000) : ℝ) = ((1000000 / 1167871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (91883901 / 500000000) ≤ -Real.log (832129 / 1000000) ∧
    -Real.log (832129 / 1000000) ≤ (183767803 / 1000000000) := by
  have h := checkLog_sound (w := (167871 / 1832129)) (n := 12)
    (lo := (91883901 / 500000000)) (hi := (183767803 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 832129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 832129) = 1/(832129 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-183767803 / 1000000000) (-91883901 / 500000000) (Real.log (832129 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (3108991 / 20000000) ≤ -Real.log (1000000 / 1168183) ∧
    -Real.log (1000000 / 1168183) ≤ (155449551 / 1000000000) := by
  have h := checkLog_sound (w := (168183 / 2168183)) (n := 12)
    (lo := (3108991 / 20000000)) (hi := (155449551 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1168183 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1168183 / 1000000) = 1/(1000000 / 1168183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (3108991 / 20000000) (155449551 / 1000000000) (Real.log (1168183 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1168183 / 1000000) = -Real.log (1000000 / 1168183) := by
    rw [show ((1168183 / 1000000) : ℝ) = ((1000000 / 1168183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (92071407 / 500000000) ≤ -Real.log (831817 / 1000000) ∧
    -Real.log (831817 / 1000000) ≤ (36828563 / 200000000) := by
  have h := checkLog_sound (w := (168183 / 1831817)) (n := 12)
    (lo := (92071407 / 500000000)) (hi := (36828563 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 831817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 831817) = 1/(831817 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-36828563 / 200000000) (-92071407 / 500000000) (Real.log (831817 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (68364071 / 100000000) ≤ -Real.log (125000000000 / 247634643377) ∧
    -Real.log (125000000000 / 247634643377) ≤ (683640711 / 1000000000) := by
  have h := checkLog_sound (w := (122634643377 / 372634643377)) (n := 12)
    (lo := (68364071 / 100000000)) (hi := (683640711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247634643377 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247634643377 / 125000000000) = 1/(125000000000 / 247634643377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (68364071 / 100000000) (683640711 / 1000000000) (Real.log (247634643377 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (247634643377 / 125000000000) = -Real.log (125000000000 / 247634643377) := by
    rw [show ((247634643377 / 125000000000) : ℝ) = ((125000000000 / 247634643377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (684955209 / 1000000000) ≤ -Real.log (250000000000 / 495920745921) ∧
    -Real.log (250000000000 / 495920745921) ≤ (68495521 / 100000000) := by
  have h := checkLog_sound (w := (245920745921 / 745920745921)) (n := 12)
    (lo := (684955209 / 1000000000)) (hi := (68495521 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((495920745921 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(495920745921 / 250000000000) = 1/(250000000000 / 495920745921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (684955209 / 1000000000) (68495521 / 100000000) (Real.log (495920745921 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (495920745921 / 250000000000) = -Real.log (250000000000 / 495920745921) := by
    rw [show ((495920745921 / 250000000000) : ℝ) = ((250000000000 / 495920745921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (19057197 / 40000000) ≤ -Real.log (500000000000 / 805157591253) ∧
    -Real.log (500000000000 / 805157591253) ≤ (238214963 / 500000000) := by
  have h := checkLog_sound (w := (305157591253 / 1305157591253)) (n := 12)
    (lo := (19057197 / 40000000)) (hi := (238214963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((805157591253 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(805157591253 / 500000000000) = 1/(500000000000 / 805157591253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (19057197 / 40000000) (238214963 / 500000000) (Real.log (805157591253 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (805157591253 / 500000000000) = -Real.log (500000000000 / 805157591253) := by
    rw [show ((805157591253 / 500000000000) : ℝ) = ((500000000000 / 805157591253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (19092913 / 40000000) ≤ -Real.log (125000000000 / 201469209383) ∧
    -Real.log (125000000000 / 201469209383) ≤ (238661413 / 500000000) := by
  have h := checkLog_sound (w := (76469209383 / 326469209383)) (n := 12)
    (lo := (19092913 / 40000000)) (hi := (238661413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((201469209383 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(201469209383 / 125000000000) = 1/(125000000000 / 201469209383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (19092913 / 40000000) (238661413 / 500000000) (Real.log (201469209383 / 125000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (201469209383 / 125000000000) = -Real.log (125000000000 / 201469209383) := by
    rw [show ((201469209383 / 125000000000) : ℝ) = ((125000000000 / 201469209383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (67790047 / 200000000) ≤ -Real.log (500000000000 / 701736749951) ∧
    -Real.log (500000000000 / 701736749951) ≤ (84737559 / 250000000) := by
  have h := checkLog_sound (w := (201736749951 / 1201736749951)) (n := 12)
    (lo := (67790047 / 200000000)) (hi := (84737559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((701736749951 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(701736749951 / 500000000000) = 1/(500000000000 / 701736749951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (67790047 / 200000000) (84737559 / 250000000) (Real.log (701736749951 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (701736749951 / 500000000000) = -Real.log (500000000000 / 701736749951) := by
    rw [show ((701736749951 / 500000000000) : ℝ) = ((500000000000 / 701736749951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (84898091 / 250000000) ≤ -Real.log (62500000000 / 87773437547) ∧
    -Real.log (62500000000 / 87773437547) ≤ (67918473 / 200000000) := by
  have h := checkLog_sound (w := (25273437547 / 150273437547)) (n := 12)
    (lo := (84898091 / 250000000)) (hi := (67918473 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87773437547 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(87773437547 / 62500000000) = 1/(62500000000 / 87773437547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (84898091 / 250000000) (67918473 / 200000000) (Real.log (87773437547 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (87773437547 / 62500000000) = -Real.log (62500000000 / 87773437547) := by
    rw [show ((87773437547 / 62500000000) : ℝ) = ((62500000000 / 87773437547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1793329 / 62500000) ≤ -Real.log (971714478511 / 1000000000000) ∧
    -Real.log (971714478511 / 1000000000000) ≤ (5738653 / 200000000) := by
  have h := checkLog_sound (w := (28285521489 / 1971714478511)) (n := 12)
    (lo := (1793329 / 62500000)) (hi := (5738653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 971714478511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 971714478511) = 1/(971714478511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-5738653 / 200000000) (-1793329 / 62500000) (Real.log (971714478511 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (28585369 / 1000000000) ≤ -Real.log (971819327359 / 1000000000000) ∧
    -Real.log (971819327359 / 1000000000000) ≤ (2858537 / 100000000) := by
  have h := checkLog_sound (w := (28180672641 / 1971819327359)) (n := 12)
    (lo := (28585369 / 1000000000)) (hi := (2858537 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 971819327359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 971819327359) = 1/(971819327359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-2858537 / 100000000) (-28585369 / 1000000000) (Real.log (971819327359 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell135
