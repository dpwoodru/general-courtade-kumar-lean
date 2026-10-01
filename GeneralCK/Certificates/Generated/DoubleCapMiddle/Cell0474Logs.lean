import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0474
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

theorem reflection_log_1_neg : (18305371 / 100000000) ≤ -Real.log (10240 / 12297) ∧
    -Real.log (10240 / 12297) ≤ (183053711 / 1000000000) := by
  have h := checkLog_sound (w := (2057 / 22537)) (n := 12)
    (lo := (18305371 / 100000000)) (hi := (183053711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12297 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12297 / 10240) = 1/(10240 / 12297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (18305371 / 100000000) (183053711 / 1000000000) (Real.log (12297 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12297 / 10240) = -Real.log (10240 / 12297) := by
    rw [show ((12297 / 10240) : ℝ) = ((10240 / 12297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (56060697 / 250000000) ≤ -Real.log (8183 / 10240) ∧
    -Real.log (8183 / 10240) ≤ (224242789 / 1000000000) := by
  have h := checkLog_sound (w := (2057 / 18423)) (n := 12)
    (lo := (56060697 / 250000000)) (hi := (224242789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 8183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 8183) = 1/(8183 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-224242789 / 1000000000) (-56060697 / 250000000) (Real.log (8183 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (91465861 / 500000000) ≤ -Real.log (20480 / 24591) ∧
    -Real.log (20480 / 24591) ≤ (182931723 / 1000000000) := by
  have h := checkLog_sound (w := (4111 / 45071)) (n := 12)
    (lo := (91465861 / 500000000)) (hi := (182931723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24591 / 20480) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24591 / 20480) = 1/(20480 / 24591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (91465861 / 500000000) (182931723 / 1000000000) (Real.log (24591 / 20480)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24591 / 20480) = -Real.log (20480 / 24591) := by
    rw [show ((24591 / 20480) : ℝ) = ((20480 / 24591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (112029749 / 500000000) ≤ -Real.log (16369 / 20480) ∧
    -Real.log (16369 / 20480) ≤ (224059499 / 1000000000) := by
  have h := checkLog_sound (w := (4111 / 36849)) (n := 12)
    (lo := (112029749 / 500000000)) (hi := (224059499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20480 / 16369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20480 / 16369) = 1/(16369 / 20480) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-224059499 / 1000000000) (-112029749 / 500000000) (Real.log (16369 / 20480)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (337727029 / 1000000000) ≤ -Real.log (5120 / 7177) ∧
    -Real.log (5120 / 7177) ≤ (33772703 / 100000000) := by
  have h := checkLog_sound (w := (2057 / 12297)) (n := 12)
    (lo := (337727029 / 1000000000)) (hi := (33772703 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7177 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7177 / 5120) = 1/(5120 / 7177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (337727029 / 1000000000) (33772703 / 100000000) (Real.log (7177 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7177 / 5120) = -Real.log (5120 / 7177) := by
    rw [show ((7177 / 5120) : ℝ) = ((5120 / 7177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (513759611 / 1000000000) ≤ -Real.log (3063 / 5120) ∧
    -Real.log (3063 / 5120) ≤ (128439903 / 250000000) := by
  have h := checkLog_sound (w := (2057 / 8183)) (n := 12)
    (lo := (513759611 / 1000000000)) (hi := (128439903 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3063) = 1/(3063 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-128439903 / 250000000) (-513759611 / 1000000000) (Real.log (3063 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (168759003 / 500000000) ≤ -Real.log (10240 / 14351) ∧
    -Real.log (10240 / 14351) ≤ (337518007 / 1000000000) := by
  have h := checkLog_sound (w := (4111 / 24591)) (n := 12)
    (lo := (168759003 / 500000000)) (hi := (337518007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14351 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14351 / 10240) = 1/(10240 / 14351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (168759003 / 500000000) (337518007 / 1000000000) (Real.log (14351 / 10240)) := by
  have h := reflection_log_7_neg
  have he : Real.log (14351 / 10240) = -Real.log (10240 / 14351) := by
    rw [show ((14351 / 10240) : ℝ) = ((10240 / 14351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (102654003 / 200000000) ≤ -Real.log (6129 / 10240) ∧
    -Real.log (6129 / 10240) ≤ (2004961 / 3906250) := by
  have h := checkLog_sound (w := (4111 / 16369)) (n := 12)
    (lo := (102654003 / 200000000)) (hi := (2004961 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 6129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 6129) = 1/(6129 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2004961 / 3906250) (-102654003 / 200000000) (Real.log (6129 / 10240)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (125738763 / 500000000) ≤ -Real.log (250000 / 321481) ∧
    -Real.log (250000 / 321481) ≤ (251477527 / 1000000000) := by
  have h := checkLog_sound (w := (71481 / 571481)) (n := 12)
    (lo := (125738763 / 500000000)) (hi := (251477527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321481 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(321481 / 250000) = 1/(250000 / 321481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (125738763 / 500000000) (251477527 / 1000000000) (Real.log (321481 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (321481 / 250000) = -Real.log (250000 / 321481) := by
    rw [show ((321481 / 250000) : ℝ) = ((250000 / 321481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (336765879 / 1000000000) ≤ -Real.log (178519 / 250000) ∧
    -Real.log (178519 / 250000) ≤ (8419147 / 25000000) := by
  have h := checkLog_sound (w := (71481 / 428519)) (n := 12)
    (lo := (336765879 / 1000000000)) (hi := (8419147 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 178519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 178519) = 1/(178519 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-8419147 / 25000000) (-336765879 / 1000000000) (Real.log (178519 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (15727697 / 62500000) ≤ -Real.log (1000000 / 1286137) ∧
    -Real.log (1000000 / 1286137) ≤ (251643153 / 1000000000) := by
  have h := checkLog_sound (w := (286137 / 2286137)) (n := 12)
    (lo := (15727697 / 62500000)) (hi := (251643153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1286137 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1286137 / 1000000) = 1/(1000000 / 1286137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (15727697 / 62500000) (251643153 / 1000000000) (Real.log (1286137 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1286137 / 1000000) = -Real.log (1000000 / 1286137) := by
    rw [show ((1286137 / 1000000) : ℝ) = ((1000000 / 1286137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (337064211 / 1000000000) ≤ -Real.log (713863 / 1000000) ∧
    -Real.log (713863 / 1000000) ≤ (84266053 / 250000000) := by
  have h := checkLog_sound (w := (286137 / 1713863)) (n := 12)
    (lo := (337064211 / 1000000000)) (hi := (84266053 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 713863) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 713863) = 1/(713863 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-84266053 / 250000000) (-337064211 / 1000000000) (Real.log (713863 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (94011801 / 500000000) ≤ -Real.log (500000 / 603431) ∧
    -Real.log (500000 / 603431) ≤ (188023603 / 1000000000) := by
  have h := checkLog_sound (w := (103431 / 1103431)) (n := 12)
    (lo := (94011801 / 500000000)) (hi := (188023603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603431 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603431 / 500000) = 1/(500000 / 603431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (94011801 / 500000000) (188023603 / 1000000000) (Real.log (603431 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (603431 / 500000) = -Real.log (500000 / 603431) := by
    rw [show ((603431 / 500000) : ℝ) = ((500000 / 603431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (231758049 / 1000000000) ≤ -Real.log (396569 / 500000) ∧
    -Real.log (396569 / 500000) ≤ (4635161 / 20000000) := by
  have h := checkLog_sound (w := (103431 / 896569)) (n := 12)
    (lo := (231758049 / 1000000000)) (hi := (4635161 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 396569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 396569) = 1/(396569 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-4635161 / 20000000) (-231758049 / 1000000000) (Real.log (396569 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (188156997 / 1000000000) ≤ -Real.log (1000000 / 1207023) ∧
    -Real.log (1000000 / 1207023) ≤ (94078499 / 500000000) := by
  have h := checkLog_sound (w := (207023 / 2207023)) (n := 12)
    (lo := (188156997 / 1000000000)) (hi := (94078499 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1207023 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1207023 / 1000000) = 1/(1000000 / 1207023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (188156997 / 1000000000) (94078499 / 500000000) (Real.log (1207023 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1207023 / 1000000) = -Real.log (1000000 / 1207023) := by
    rw [show ((1207023 / 1000000) : ℝ) = ((1000000 / 1207023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (231961061 / 1000000000) ≤ -Real.log (792977 / 1000000) ∧
    -Real.log (792977 / 1000000) ≤ (115980531 / 500000000) := by
  have h := checkLog_sound (w := (207023 / 1792977)) (n := 12)
    (lo := (231961061 / 1000000000)) (hi := (115980531 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 792977) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 792977) = 1/(792977 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-115980531 / 500000000) (-231961061 / 1000000000) (Real.log (792977 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (117648681 / 200000000) ≤ -Real.log (125000000000 / 225102790179) ∧
    -Real.log (125000000000 / 225102790179) ≤ (294121703 / 500000000) := by
  have h := checkLog_sound (w := (100102790179 / 350102790179)) (n := 12)
    (lo := (117648681 / 200000000)) (hi := (294121703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((225102790179 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(225102790179 / 125000000000) = 1/(125000000000 / 225102790179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (117648681 / 200000000) (294121703 / 500000000) (Real.log (225102790179 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (225102790179 / 125000000000) = -Real.log (125000000000 / 225102790179) := by
    rw [show ((225102790179 / 125000000000) : ℝ) = ((125000000000 / 225102790179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (588707363 / 1000000000) ≤ -Real.log (500000000000 / 900829010609) ∧
    -Real.log (500000000000 / 900829010609) ≤ (147176841 / 250000000) := by
  have h := checkLog_sound (w := (400829010609 / 1400829010609)) (n := 12)
    (lo := (588707363 / 1000000000)) (hi := (147176841 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((900829010609 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(900829010609 / 500000000000) = 1/(500000000000 / 900829010609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (588707363 / 1000000000) (147176841 / 250000000) (Real.log (900829010609 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (900829010609 / 500000000000) = -Real.log (500000000000 / 900829010609) := by
    rw [show ((900829010609 / 500000000000) : ℝ) = ((500000000000 / 900829010609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (104945413 / 250000000) ≤ -Real.log (500000000000 / 760814637553) ∧
    -Real.log (500000000000 / 760814637553) ≤ (419781653 / 1000000000) := by
  have h := checkLog_sound (w := (260814637553 / 1260814637553)) (n := 12)
    (lo := (104945413 / 250000000)) (hi := (419781653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((760814637553 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(760814637553 / 500000000000) = 1/(500000000000 / 760814637553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (104945413 / 250000000) (419781653 / 1000000000) (Real.log (760814637553 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (760814637553 / 500000000000) = -Real.log (500000000000 / 760814637553) := by
    rw [show ((760814637553 / 500000000000) : ℝ) = ((500000000000 / 760814637553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (210059029 / 500000000) ≤ -Real.log (500000000000 / 761070623739) ∧
    -Real.log (500000000000 / 761070623739) ≤ (420118059 / 1000000000) := by
  have h := checkLog_sound (w := (261070623739 / 1261070623739)) (n := 12)
    (lo := (210059029 / 500000000)) (hi := (420118059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((761070623739 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(761070623739 / 500000000000) = 1/(500000000000 / 761070623739) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (210059029 / 500000000) (420118059 / 1000000000) (Real.log (761070623739 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (761070623739 / 500000000000) = -Real.log (500000000000 / 761070623739) := by
    rw [show ((761070623739 / 500000000000) : ℝ) = ((500000000000 / 761070623739) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0474
