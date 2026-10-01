import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell154
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

theorem reflection_log_1_neg : (183301 / 625000) ≤ -Real.log (1024 / 1373) ∧
    -Real.log (1024 / 1373) ≤ (293281601 / 1000000000) := by
  have h := checkLog_sound (w := (349 / 2397)) (n := 12)
    (lo := (183301 / 625000)) (hi := (293281601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1373 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1373 / 1024) = 1/(1024 / 1373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (183301 / 625000) (293281601 / 1000000000) (Real.log (1373 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1373 / 1024) = -Real.log (1024 / 1373) := by
    rw [show ((1373 / 1024) : ℝ) = ((1024 / 1373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (208379557 / 500000000) ≤ -Real.log (675 / 1024) ∧
    -Real.log (675 / 1024) ≤ (83351823 / 200000000) := by
  have h := checkLog_sound (w := (349 / 1699)) (n := 12)
    (lo := (208379557 / 500000000)) (hi := (83351823 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 675) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 675) = 1/(675 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-83351823 / 200000000) (-208379557 / 500000000) (Real.log (675 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (58568901 / 200000000) ≤ -Real.log (2560 / 3431) ∧
    -Real.log (2560 / 3431) ≤ (146422253 / 500000000) := by
  have h := checkLog_sound (w := (871 / 5991)) (n := 12)
    (lo := (58568901 / 200000000)) (hi := (146422253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3431 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3431 / 2560) = 1/(2560 / 3431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (58568901 / 200000000) (146422253 / 500000000) (Real.log (3431 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3431 / 2560) = -Real.log (2560 / 3431) := by
    rw [show ((3431 / 2560) : ℝ) = ((2560 / 3431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (20793531 / 50000000) ≤ -Real.log (1689 / 2560) ∧
    -Real.log (1689 / 2560) ≤ (415870621 / 1000000000) := by
  have h := checkLog_sound (w := (871 / 4249)) (n := 12)
    (lo := (20793531 / 50000000)) (hi := (415870621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1689) = 1/(1689 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-415870621 / 1000000000) (-20793531 / 50000000) (Real.log (1689 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (43312549 / 200000000) ≤ -Real.log (1000000 / 1241801) ∧
    -Real.log (1000000 / 1241801) ≤ (108281373 / 500000000) := by
  have h := checkLog_sound (w := (241801 / 2241801)) (n := 12)
    (lo := (43312549 / 200000000)) (hi := (108281373 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1241801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1241801 / 1000000) = 1/(1000000 / 1241801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (43312549 / 200000000) (108281373 / 500000000) (Real.log (1241801 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1241801 / 1000000) = -Real.log (1000000 / 1241801) := by
    rw [show ((1241801 / 1000000) : ℝ) = ((1000000 / 1241801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (138404697 / 500000000) ≤ -Real.log (758199 / 1000000) ∧
    -Real.log (758199 / 1000000) ≤ (55361879 / 200000000) := by
  have h := checkLog_sound (w := (241801 / 1758199)) (n := 12)
    (lo := (138404697 / 500000000)) (hi := (55361879 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 758199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 758199) = 1/(758199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-55361879 / 200000000) (-138404697 / 500000000) (Real.log (758199 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (54225629 / 250000000) ≤ -Real.log (1000000 / 1242223) ∧
    -Real.log (1000000 / 1242223) ≤ (216902517 / 1000000000) := by
  have h := checkLog_sound (w := (242223 / 2242223)) (n := 12)
    (lo := (54225629 / 250000000)) (hi := (216902517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1242223 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1242223 / 1000000) = 1/(1000000 / 1242223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (54225629 / 250000000) (216902517 / 1000000000) (Real.log (1242223 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1242223 / 1000000) = -Real.log (1000000 / 1242223) := by
    rw [show ((1242223 / 1000000) : ℝ) = ((1000000 / 1242223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (277366131 / 1000000000) ≤ -Real.log (757777 / 1000000) ∧
    -Real.log (757777 / 1000000) ≤ (69341533 / 250000000) := by
  have h := checkLog_sound (w := (242223 / 1757777)) (n := 12)
    (lo := (277366131 / 1000000000)) (hi := (69341533 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 757777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 757777) = 1/(757777 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-69341533 / 250000000) (-277366131 / 1000000000) (Real.log (757777 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (160241237 / 1000000000) ≤ -Real.log (500000 / 586897) ∧
    -Real.log (500000 / 586897) ≤ (80120619 / 500000000) := by
  have h := checkLog_sound (w := (86897 / 1086897)) (n := 12)
    (lo := (160241237 / 1000000000)) (hi := (80120619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586897 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586897 / 500000) = 1/(500000 / 586897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (160241237 / 1000000000) (80120619 / 500000000) (Real.log (586897 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (586897 / 500000) = -Real.log (500000 / 586897) := by
    rw [show ((586897 / 500000) : ℝ) = ((500000 / 586897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (190911141 / 1000000000) ≤ -Real.log (413103 / 500000) ∧
    -Real.log (413103 / 500000) ≤ (95455571 / 500000000) := by
  have h := checkLog_sound (w := (86897 / 913103)) (n := 12)
    (lo := (190911141 / 1000000000)) (hi := (95455571 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 413103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 413103) = 1/(413103 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-95455571 / 500000000) (-190911141 / 1000000000) (Real.log (413103 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (16050871 / 100000000) ≤ -Real.log (250000 / 293527) ∧
    -Real.log (250000 / 293527) ≤ (160508711 / 1000000000) := by
  have h := checkLog_sound (w := (43527 / 543527)) (n := 12)
    (lo := (16050871 / 100000000)) (hi := (160508711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293527 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293527 / 250000) = 1/(250000 / 293527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (16050871 / 100000000) (160508711 / 1000000000) (Real.log (293527 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (293527 / 250000) = -Real.log (250000 / 293527) := by
    rw [show ((293527 / 250000) : ℝ) = ((250000 / 293527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1494463 / 7812500) ≤ -Real.log (206473 / 250000) ∧
    -Real.log (206473 / 250000) ≤ (38258253 / 200000000) := by
  have h := checkLog_sound (w := (43527 / 456473)) (n := 12)
    (lo := (1494463 / 7812500)) (hi := (38258253 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 206473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 206473) = 1/(206473 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-38258253 / 200000000) (-1494463 / 7812500) (Real.log (206473 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (5669721 / 8000000) ≤ -Real.log (125000000000 / 253922439313) ∧
    -Real.log (125000000000 / 253922439313) ≤ (708715127 / 1000000000) := by
  have h := checkLog_sound (w := (3922439313 / 503922439313)) (n := 12)
    (lo := (3113589 / 200000000)) (hi := (7783973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((253922439313 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(253922439313 / 250000000000) = 1/(125000000000 / 253922439313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (5669721 / 8000000) (708715127 / 1000000000) (Real.log (253922439313 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (253922439313 / 125000000000) = -Real.log (125000000000 / 253922439313) := by
    rw [show ((253922439313 / 125000000000) : ℝ) = ((125000000000 / 253922439313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (355020357 / 500000000) ≤ -Real.log (250000000000 / 508518518519) ∧
    -Real.log (250000000000 / 508518518519) ≤ (177510179 / 250000000) := by
  have h := checkLog_sound (w := (8518518519 / 1008518518519)) (n := 12)
    (lo := (8446767 / 500000000)) (hi := (3378707 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((508518518519 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(508518518519 / 500000000000) = 1/(250000000000 / 508518518519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (355020357 / 500000000) (177510179 / 250000000) (Real.log (508518518519 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (508518518519 / 250000000000) = -Real.log (250000000000 / 508518518519) := by
    rw [show ((508518518519 / 250000000000) : ℝ) = ((250000000000 / 508518518519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (24668607 / 50000000) ≤ -Real.log (125000000000 / 204728738761) ∧
    -Real.log (125000000000 / 204728738761) ≤ (493372141 / 1000000000) := by
  have h := checkLog_sound (w := (79728738761 / 329728738761)) (n := 12)
    (lo := (24668607 / 50000000)) (hi := (493372141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204728738761 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(204728738761 / 125000000000) = 1/(125000000000 / 204728738761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (24668607 / 50000000) (493372141 / 1000000000) (Real.log (204728738761 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (204728738761 / 125000000000) = -Real.log (125000000000 / 204728738761) := by
    rw [show ((204728738761 / 125000000000) : ℝ) = ((125000000000 / 204728738761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (61783581 / 125000000) ≤ -Real.log (500000000000 / 819649448321) ∧
    -Real.log (500000000000 / 819649448321) ≤ (494268649 / 1000000000) := by
  have h := checkLog_sound (w := (319649448321 / 1319649448321)) (n := 12)
    (lo := (61783581 / 125000000)) (hi := (494268649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819649448321 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819649448321 / 500000000000) = 1/(500000000000 / 819649448321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (61783581 / 125000000) (494268649 / 1000000000) (Real.log (819649448321 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (819649448321 / 500000000000) = -Real.log (500000000000 / 819649448321) := by
    rw [show ((819649448321 / 500000000000) : ℝ) = ((500000000000 / 819649448321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (351152379 / 1000000000) ≤ -Real.log (50000000000 / 71035189771) ∧
    -Real.log (50000000000 / 71035189771) ≤ (17557619 / 50000000) := by
  have h := checkLog_sound (w := (21035189771 / 121035189771)) (n := 12)
    (lo := (351152379 / 1000000000)) (hi := (17557619 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71035189771 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71035189771 / 50000000000) = 1/(50000000000 / 71035189771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (351152379 / 1000000000) (17557619 / 50000000) (Real.log (71035189771 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (71035189771 / 50000000000) = -Real.log (50000000000 / 71035189771) := by
    rw [show ((71035189771 / 50000000000) : ℝ) = ((50000000000 / 71035189771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (175899987 / 500000000) ≤ -Real.log (250000000000 / 355406033719) ∧
    -Real.log (250000000000 / 355406033719) ≤ (14071999 / 40000000) := by
  have h := checkLog_sound (w := (105406033719 / 605406033719)) (n := 12)
    (lo := (175899987 / 500000000)) (hi := (14071999 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355406033719 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355406033719 / 250000000000) = 1/(250000000000 / 355406033719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (175899987 / 500000000) (14071999 / 40000000) (Real.log (355406033719 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (355406033719 / 250000000000) = -Real.log (250000000000 / 355406033719) := by
    rw [show ((355406033719 / 250000000000) : ℝ) = ((250000000000 / 355406033719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (15391277 / 500000000) ≤ -Real.log (60605400271 / 62500000000) ∧
    -Real.log (60605400271 / 62500000000) ≤ (6156511 / 200000000) := by
  have h := checkLog_sound (w := (1894599729 / 123105400271)) (n := 12)
    (lo := (15391277 / 500000000)) (hi := (6156511 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60605400271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60605400271) = 1/(60605400271 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-6156511 / 200000000) (-15391277 / 500000000) (Real.log (60605400271 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1916869 / 62500000) ≤ -Real.log (242448911391 / 250000000000) ∧
    -Real.log (242448911391 / 250000000000) ≤ (6133981 / 200000000) := by
  have h := checkLog_sound (w := (7551088609 / 492448911391)) (n := 12)
    (lo := (1916869 / 62500000)) (hi := (6133981 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242448911391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242448911391) = 1/(242448911391 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-6133981 / 200000000) (-1916869 / 62500000) (Real.log (242448911391 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell154
