import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0096
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

theorem reflection_log_1_neg : (336083453 / 500000000) ≤ -Real.log (25600 / 50137) ∧
    -Real.log (25600 / 50137) ≤ (672166907 / 1000000000) := by
  have h := checkLog_sound (w := (24537 / 75737)) (n := 12)
    (lo := (336083453 / 500000000)) (hi := (672166907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50137 / 25600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50137 / 25600) = 1/(25600 / 50137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (336083453 / 500000000) (672166907 / 1000000000) (Real.log (50137 / 25600)) := by
  have h := reflection_log_1_neg
  have he : Real.log (50137 / 25600) = -Real.log (25600 / 50137) := by
    rw [show ((50137 / 25600) : ℝ) = ((25600 / 50137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (3181497249 / 1000000000) ≤ -Real.log (1063 / 25600) ∧
    -Real.log (1063 / 25600) ≤ (1590748627 / 500000000) := by
  have h := checkLog_sound (w := (537 / 2663)) (n := 12)
    (lo := (408908529 / 1000000000)) (hi := (40890853 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1063) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1600 / 1063) = 1/(1063 / 25600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-1590748627 / 500000000) (-3181497249 / 1000000000) (Real.log (1063 / 25600)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (10499647 / 15625000) ≤ -Real.log (10240 / 20051) ∧
    -Real.log (10240 / 20051) ≤ (671977409 / 1000000000) := by
  have h := checkLog_sound (w := (9811 / 30291)) (n := 12)
    (lo := (10499647 / 15625000)) (hi := (671977409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20051 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20051 / 10240) = 1/(10240 / 20051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (10499647 / 15625000) (671977409 / 1000000000) (Real.log (20051 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (20051 / 10240) = -Real.log (10240 / 20051) := by
    rw [show ((20051 / 10240) : ℝ) = ((10240 / 20051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (3172599977 / 1000000000) ≤ -Real.log (429 / 10240) ∧
    -Real.log (429 / 10240) ≤ (1586299991 / 500000000) := by
  have h := checkLog_sound (w := (211 / 1069)) (n := 12)
    (lo := (400011257 / 1000000000)) (hi := (200005629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 429) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(640 / 429) = 1/(429 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1586299991 / 500000000) (-3172599977 / 1000000000) (Real.log (429 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (650737011 / 1000000000) ≤ -Real.log (12800 / 24537) ∧
    -Real.log (12800 / 24537) ≤ (162684253 / 250000000) := by
  have h := checkLog_sound (w := (11737 / 37337)) (n := 12)
    (lo := (650737011 / 1000000000)) (hi := (162684253 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24537 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24537 / 12800) = 1/(12800 / 24537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (650737011 / 1000000000) (162684253 / 250000000) (Real.log (24537 / 12800)) := by
  have h := reflection_log_5_neg
  have he : Real.log (24537 / 12800) = -Real.log (12800 / 24537) := by
    rw [show ((24537 / 12800) : ℝ) = ((12800 / 24537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2488350069 / 1000000000) ≤ -Real.log (1063 / 12800) ∧
    -Real.log (1063 / 12800) ≤ (2488350073 / 1000000000) := by
  have h := checkLog_sound (w := (537 / 2663)) (n := 12)
    (lo := (408908529 / 1000000000)) (hi := (40890853 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1063) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1063) = 1/(1063 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2488350073 / 1000000000) (-2488350069 / 1000000000) (Real.log (1063 / 12800)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (325174883 / 500000000) ≤ -Real.log (5120 / 9811) ∧
    -Real.log (5120 / 9811) ≤ (650349767 / 1000000000) := by
  have h := checkLog_sound (w := (4691 / 14931)) (n := 12)
    (lo := (325174883 / 500000000)) (hi := (650349767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9811 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9811 / 5120) = 1/(5120 / 9811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (325174883 / 500000000) (650349767 / 1000000000) (Real.log (9811 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (9811 / 5120) = -Real.log (5120 / 9811) := by
    rw [show ((9811 / 5120) : ℝ) = ((5120 / 9811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2479452797 / 1000000000) ≤ -Real.log (429 / 5120) ∧
    -Real.log (429 / 5120) ≤ (2479452801 / 1000000000) := by
  have h := checkLog_sound (w := (211 / 1069)) (n := 12)
    (lo := (400011257 / 1000000000)) (hi := (200005629 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 429) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(640 / 429) = 1/(429 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2479452801 / 1000000000) (-2479452797 / 1000000000) (Real.log (429 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (675790419 / 1000000000) ≤ -Real.log (500000 / 982793) ∧
    -Real.log (500000 / 982793) ≤ (33789521 / 50000000) := by
  have h := checkLog_sound (w := (482793 / 1482793)) (n := 12)
    (lo := (675790419 / 1000000000)) (hi := (33789521 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((982793 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(982793 / 500000) = 1/(500000 / 982793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (675790419 / 1000000000) (33789521 / 50000000) (Real.log (982793 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (982793 / 500000) = -Real.log (500000 / 982793) := by
    rw [show ((982793 / 500000) : ℝ) = ((500000 / 982793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1684645909 / 500000000) ≤ -Real.log (17207 / 500000) ∧
    -Real.log (17207 / 500000) ≤ (3369291823 / 1000000000) := by
  have h := checkLog_sound (w := (14043 / 48457)) (n := 12)
    (lo := (298351549 / 500000000)) (hi := (596703099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17207) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 17207) = 1/(17207 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-3369291823 / 1000000000) (-1684645909 / 500000000) (Real.log (17207 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (67593693 / 100000000) ≤ -Real.log (500000 / 982937) ∧
    -Real.log (500000 / 982937) ≤ (675936931 / 1000000000) := by
  have h := checkLog_sound (w := (482937 / 1482937)) (n := 12)
    (lo := (67593693 / 100000000)) (hi := (675936931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((982937 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(982937 / 500000) = 1/(500000 / 982937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (67593693 / 100000000) (675936931 / 1000000000) (Real.log (982937 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (982937 / 500000) = -Real.log (500000 / 982937) := by
    rw [show ((982937 / 500000) : ℝ) = ((500000 / 982937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3377695719 / 1000000000) ≤ -Real.log (17063 / 500000) ∧
    -Real.log (17063 / 500000) ≤ (844423931 / 250000000) := by
  have h := checkLog_sound (w := (14187 / 48313)) (n := 12)
    (lo := (605106999 / 1000000000)) (hi := (605107 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17063) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(31250 / 17063) = 1/(17063 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-844423931 / 250000000) (-3377695719 / 1000000000) (Real.log (17063 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (675626587 / 1000000000) ≤ -Real.log (62500 / 122829) ∧
    -Real.log (62500 / 122829) ≤ (168906647 / 250000000) := by
  have h := checkLog_sound (w := (60329 / 185329)) (n := 12)
    (lo := (675626587 / 1000000000)) (hi := (168906647 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((122829 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(122829 / 62500) = 1/(62500 / 122829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (675626587 / 1000000000) (168906647 / 250000000) (Real.log (122829 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (122829 / 62500) = -Real.log (62500 / 122829) := by
    rw [show ((122829 / 62500) : ℝ) = ((62500 / 122829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (3359978663 / 1000000000) ≤ -Real.log (2171 / 62500) ∧
    -Real.log (2171 / 62500) ≤ (839994667 / 250000000) := by
  have h := checkLog_sound (w := (6941 / 24309)) (n := 12)
    (lo := (587389943 / 1000000000)) (hi := (73423743 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 8684) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(15625 / 8684) = 1/(2171 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-839994667 / 250000000) (-3359978663 / 1000000000) (Real.log (2171 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (675776683 / 1000000000) ≤ -Real.log (1000000 / 1965559) ∧
    -Real.log (1000000 / 1965559) ≤ (168944171 / 250000000) := by
  have h := checkLog_sound (w := (965559 / 2965559)) (n := 12)
    (lo := (675776683 / 1000000000)) (hi := (168944171 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1965559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1965559 / 1000000) = 1/(1000000 / 1965559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (675776683 / 1000000000) (168944171 / 250000000) (Real.log (1965559 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1965559 / 1000000) = -Real.log (1000000 / 1965559) := by
    rw [show ((1965559 / 1000000) : ℝ) = ((1000000 / 1965559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (3368507561 / 1000000000) ≤ -Real.log (34441 / 1000000) ∧
    -Real.log (34441 / 1000000) ≤ (1684253783 / 500000000) := by
  have h := checkLog_sound (w := (28059 / 96941)) (n := 12)
    (lo := (595918841 / 1000000000)) (hi := (297959421 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 34441) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(62500 / 34441) = 1/(34441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1684253783 / 500000000) (-3368507561 / 1000000000) (Real.log (34441 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (4045082237 / 1000000000) ≤ -Real.log (500000000000 / 28557941535421) ∧
    -Real.log (500000000000 / 28557941535421) ≤ (4045082243 / 1000000000) := by
  have h := checkLog_sound (w := (12557941535421 / 44557941535421)) (n := 12)
    (lo := (579346337 / 1000000000)) (hi := (289673169 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28557941535421 / 16000000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(28557941535421 / 16000000000000) = 1/(500000000000 / 28557941535421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (4045082237 / 1000000000) (4045082243 / 1000000000) (Real.log (28557941535421 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (28557941535421 / 500000000000) = -Real.log (500000000000 / 28557941535421) := by
    rw [show ((28557941535421 / 500000000000) : ℝ) = ((500000000000 / 28557941535421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (4053632649 / 1000000000) ≤ -Real.log (25000000000 / 1440158530153) ∧
    -Real.log (25000000000 / 1440158530153) ≤ (810726531 / 200000000) := by
  have h := checkLog_sound (w := (640158530153 / 2240158530153)) (n := 12)
    (lo := (587896749 / 1000000000)) (hi := (2351587 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1440158530153 / 800000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1440158530153 / 800000000000) = 1/(25000000000 / 1440158530153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (4053632649 / 1000000000) (810726531 / 200000000) (Real.log (1440158530153 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1440158530153 / 25000000000) = -Real.log (25000000000 / 1440158530153) := by
    rw [show ((1440158530153 / 25000000000) : ℝ) = ((25000000000 / 1440158530153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (16142421 / 4000000) ≤ -Real.log (15625000000 / 884018021649) ∧
    -Real.log (15625000000 / 884018021649) ≤ (504450657 / 125000000) := by
  have h := checkLog_sound (w := (384018021649 / 1384018021649)) (n := 12)
    (lo := (11397387 / 20000000)) (hi := (569869351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((884018021649 / 500000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(884018021649 / 500000000000) = 1/(15625000000 / 884018021649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (16142421 / 4000000) (504450657 / 125000000) (Real.log (884018021649 / 15625000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (884018021649 / 15625000000) = -Real.log (15625000000 / 884018021649) := by
    rw [show ((884018021649 / 15625000000) : ℝ) = ((15625000000 / 884018021649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1011071061 / 250000000) ≤ -Real.log (20000000000 / 1141406463227) ∧
    -Real.log (20000000000 / 1141406463227) ≤ (16177137 / 4000000) := by
  have h := checkLog_sound (w := (501406463227 / 1781406463227)) (n := 12)
    (lo := (72318543 / 125000000)) (hi := (115709669 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1141406463227 / 640000000000) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(1141406463227 / 640000000000) = 1/(20000000000 / 1141406463227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1011071061 / 250000000) (16177137 / 4000000) (Real.log (1141406463227 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1141406463227 / 20000000000) = -Real.log (20000000000 / 1141406463227) := by
    rw [show ((1141406463227 / 20000000000) : ℝ) = ((20000000000 / 1141406463227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0096
