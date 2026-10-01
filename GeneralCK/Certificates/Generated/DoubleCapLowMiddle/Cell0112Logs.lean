import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0112
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

theorem reflection_log_1_neg : (41820663 / 62500000) ≤ -Real.log (5120 / 9997) ∧
    -Real.log (5120 / 9997) ≤ (669130609 / 1000000000) := by
  have h := checkLog_sound (w := (4877 / 15117)) (n := 12)
    (lo := (41820663 / 62500000)) (hi := (669130609 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9997 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9997 / 5120) = 1/(5120 / 9997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (41820663 / 62500000) (669130609 / 1000000000) (Real.log (9997 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (9997 / 5120) = -Real.log (5120 / 9997) := by
    rw [show ((9997 / 5120) : ℝ) = ((5120 / 9997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (190490517 / 62500000) ≤ -Real.log (243 / 5120) ∧
    -Real.log (243 / 5120) ≤ (3047848277 / 1000000000) := by
  have h := checkLog_sound (w := (77 / 563)) (n := 12)
    (lo := (8601861 / 31250000)) (hi := (275259553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 243) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(320 / 243) = 1/(243 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-3047848277 / 1000000000) (-190490517 / 62500000) (Real.log (243 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (334375211 / 500000000) ≤ -Real.log (12800 / 24983) ∧
    -Real.log (12800 / 24983) ≤ (668750423 / 1000000000) := by
  have h := checkLog_sound (w := (12183 / 37783)) (n := 12)
    (lo := (334375211 / 500000000)) (hi := (668750423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24983 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24983 / 12800) = 1/(12800 / 24983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (334375211 / 500000000) (668750423 / 1000000000) (Real.log (24983 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24983 / 12800) = -Real.log (12800 / 24983) := by
    rw [show ((24983 / 12800) : ℝ) = ((12800 / 24983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3032331423 / 1000000000) ≤ -Real.log (617 / 12800) ∧
    -Real.log (617 / 12800) ≤ (758082857 / 250000000) := by
  have h := checkLog_sound (w := (183 / 1417)) (n := 12)
    (lo := (259742703 / 1000000000)) (hi := (16233919 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 617) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(800 / 617) = 1/(617 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-758082857 / 250000000) (-3032331423 / 1000000000) (Real.log (617 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (322261509 / 500000000) ≤ -Real.log (2560 / 4877) ∧
    -Real.log (2560 / 4877) ≤ (644523019 / 1000000000) := by
  have h := checkLog_sound (w := (2317 / 7437)) (n := 12)
    (lo := (322261509 / 500000000)) (hi := (644523019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4877 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4877 / 2560) = 1/(2560 / 4877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (322261509 / 500000000) (644523019 / 1000000000) (Real.log (4877 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (4877 / 2560) = -Real.log (2560 / 4877) := by
    rw [show ((4877 / 2560) : ℝ) = ((2560 / 4877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (588675273 / 250000000) ≤ -Real.log (243 / 2560) ∧
    -Real.log (243 / 2560) ≤ (294337637 / 125000000) := by
  have h := checkLog_sound (w := (77 / 563)) (n := 12)
    (lo := (8601861 / 31250000)) (hi := (275259553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((320 / 243) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(320 / 243) = 1/(243 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-294337637 / 125000000) (-588675273 / 250000000) (Real.log (243 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (643743547 / 1000000000) ≤ -Real.log (6400 / 12183) ∧
    -Real.log (6400 / 12183) ≤ (160935887 / 250000000) := by
  have h := checkLog_sound (w := (5783 / 18583)) (n := 12)
    (lo := (643743547 / 1000000000)) (hi := (160935887 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12183 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12183 / 6400) = 1/(6400 / 12183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (643743547 / 1000000000) (160935887 / 250000000) (Real.log (12183 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (12183 / 6400) = -Real.log (6400 / 12183) := by
    rw [show ((12183 / 6400) : ℝ) = ((6400 / 12183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2339184243 / 1000000000) ≤ -Real.log (617 / 6400) ∧
    -Real.log (617 / 6400) ≤ (2339184247 / 1000000000) := by
  have h := checkLog_sound (w := (183 / 1417)) (n := 12)
    (lo := (259742703 / 1000000000)) (hi := (16233919 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((800 / 617) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(800 / 617) = 1/(617 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2339184247 / 1000000000) (-2339184243 / 1000000000) (Real.log (617 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (673321953 / 1000000000) ≤ -Real.log (50000 / 98037) ∧
    -Real.log (50000 / 98037) ≤ (336660977 / 500000000) := by
  have h := checkLog_sound (w := (48037 / 148037)) (n := 12)
    (lo := (673321953 / 1000000000)) (hi := (336660977 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((98037 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(98037 / 50000) = 1/(50000 / 98037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (673321953 / 1000000000) (336660977 / 500000000) (Real.log (98037 / 50000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (98037 / 50000) = -Real.log (50000 / 98037) := by
    rw [show ((98037 / 50000) : ℝ) = ((50000 / 98037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (3237549087 / 1000000000) ≤ -Real.log (1963 / 50000) ∧
    -Real.log (1963 / 50000) ≤ (809387273 / 250000000) := by
  have h := checkLog_sound (w := (581 / 2544)) (n := 12)
    (lo := (464960367 / 1000000000)) (hi := (29060023 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 1963) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(3125 / 1963) = 1/(1963 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-809387273 / 250000000) (-3237549087 / 1000000000) (Real.log (1963 / 50000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (673611087 / 1000000000) ≤ -Real.log (1000000 / 1961307) ∧
    -Real.log (1000000 / 1961307) ≤ (42100693 / 62500000) := by
  have h := checkLog_sound (w := (961307 / 2961307)) (n := 12)
    (lo := (673611087 / 1000000000)) (hi := (42100693 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1961307 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1961307 / 1000000) = 1/(1000000 / 1961307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (673611087 / 1000000000) (42100693 / 62500000) (Real.log (1961307 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1961307 / 1000000) = -Real.log (1000000 / 1961307) := by
    rw [show ((1961307 / 1000000) : ℝ) = ((1000000 / 1961307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3252096571 / 1000000000) ≤ -Real.log (38693 / 1000000) ∧
    -Real.log (38693 / 1000000) ≤ (50814009 / 15625000) := by
  have h := checkLog_sound (w := (23807 / 101193)) (n := 12)
    (lo := (479507851 / 1000000000)) (hi := (119876963 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 38693) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 38693) = 1/(38693 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-50814009 / 15625000) (-3252096571 / 1000000000) (Real.log (38693 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (336548251 / 500000000) ≤ -Real.log (500000 / 980149) ∧
    -Real.log (500000 / 980149) ≤ (673096503 / 1000000000) := by
  have h := checkLog_sound (w := (480149 / 1480149)) (n := 12)
    (lo := (336548251 / 500000000)) (hi := (673096503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((980149 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(980149 / 500000) = 1/(500000 / 980149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (336548251 / 500000000) (673096503 / 1000000000) (Real.log (980149 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (980149 / 500000) = -Real.log (500000 / 980149) := by
    rw [show ((980149 / 500000) : ℝ) = ((500000 / 980149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (201647107 / 62500000) ≤ -Real.log (19851 / 500000) ∧
    -Real.log (19851 / 500000) ≤ (3226353717 / 1000000000) := by
  have h := checkLog_sound (w := (11399 / 51101)) (n := 12)
    (lo := (3545039 / 7812500)) (hi := (453764993 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19851) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 19851) = 1/(19851 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-3226353717 / 1000000000) (-201647107 / 62500000) (Real.log (19851 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (336696931 / 500000000) ≤ -Real.log (1000000 / 1960881) ∧
    -Real.log (1000000 / 1960881) ≤ (673393863 / 1000000000) := by
  have h := checkLog_sound (w := (960881 / 2960881)) (n := 12)
    (lo := (336696931 / 500000000)) (hi := (673393863 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1960881 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1960881 / 1000000) = 1/(1000000 / 1960881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (336696931 / 500000000) (673393863 / 1000000000) (Real.log (1960881 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1960881 / 1000000) = -Real.log (1000000 / 1960881) := by
    rw [show ((1960881 / 1000000) : ℝ) = ((1000000 / 1960881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1620573497 / 500000000) ≤ -Real.log (39119 / 1000000) ∧
    -Real.log (39119 / 1000000) ≤ (3241146999 / 1000000000) := by
  have h := checkLog_sound (w := (23381 / 101619)) (n := 12)
    (lo := (234279137 / 500000000)) (hi := (18742331 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 39119) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 39119) = 1/(39119 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-3241146999 / 1000000000) (-1620573497 / 500000000) (Real.log (39119 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1527684 / 390625) ≤ -Real.log (500000000000 / 24971217524197) ∧
    -Real.log (500000000000 / 24971217524197) ≤ (1955435523 / 500000000) := by
  have h := checkLog_sound (w := (8971217524197 / 40971217524197)) (n := 12)
    (lo := (22256757 / 50000000)) (hi := (445135141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24971217524197 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(24971217524197 / 16000000000000) = 1/(500000000000 / 24971217524197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1527684 / 390625) (1955435523 / 500000000) (Real.log (24971217524197 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (24971217524197 / 500000000000) = -Real.log (500000000000 / 24971217524197) := by
    rw [show ((24971217524197 / 500000000000) : ℝ) = ((500000000000 / 24971217524197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1962853829 / 500000000) ≤ -Real.log (500000000000 / 25344467991627) ∧
    -Real.log (500000000000 / 25344467991627) ≤ (245356729 / 62500000) := by
  have h := checkLog_sound (w := (9344467991627 / 41344467991627)) (n := 12)
    (lo := (229985879 / 500000000)) (hi := (459971759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25344467991627 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(25344467991627 / 16000000000000) = 1/(500000000000 / 25344467991627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1962853829 / 500000000) (245356729 / 62500000) (Real.log (25344467991627 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (25344467991627 / 500000000000) = -Real.log (500000000000 / 25344467991627) := by
    rw [show ((25344467991627 / 500000000000) : ℝ) = ((500000000000 / 25344467991627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1949725107 / 500000000) ≤ -Real.log (500000000000 / 24687647977431) ∧
    -Real.log (500000000000 / 24687647977431) ≤ (194972511 / 50000000) := by
  have h := checkLog_sound (w := (8687647977431 / 40687647977431)) (n := 12)
    (lo := (216857157 / 500000000)) (hi := (86742863 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24687647977431 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(24687647977431 / 16000000000000) = 1/(500000000000 / 24687647977431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1949725107 / 500000000) (194972511 / 50000000) (Real.log (24687647977431 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (24687647977431 / 500000000000) = -Real.log (500000000000 / 24687647977431) := by
    rw [show ((24687647977431 / 500000000000) : ℝ) = ((500000000000 / 24687647977431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (782908171 / 200000000) ≤ -Real.log (100000000000 / 5012605127943) ∧
    -Real.log (100000000000 / 5012605127943) ≤ (3914540861 / 1000000000) := by
  have h := checkLog_sound (w := (1812605127943 / 8212605127943)) (n := 12)
    (lo := (89760991 / 200000000)) (hi := (112201239 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5012605127943 / 3200000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(5012605127943 / 3200000000000) = 1/(100000000000 / 5012605127943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (782908171 / 200000000) (3914540861 / 1000000000) (Real.log (5012605127943 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (5012605127943 / 100000000000) = -Real.log (100000000000 / 5012605127943) := by
    rw [show ((5012605127943 / 100000000000) : ℝ) = ((100000000000 / 5012605127943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0112
