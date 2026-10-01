import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell129
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

theorem reflection_log_1_neg : (141148251 / 500000000) ≤ -Real.log (512 / 679) ∧
    -Real.log (512 / 679) ≤ (282296503 / 1000000000) := by
  have h := checkLog_sound (w := (167 / 1191)) (n := 12)
    (lo := (141148251 / 500000000)) (hi := (282296503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679 / 512) = 1/(512 / 679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (141148251 / 500000000) (282296503 / 1000000000) (Real.log (679 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (679 / 512) = -Real.log (512 / 679) := by
    rw [show ((679 / 512) : ℝ) = ((512 / 679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (24673763 / 62500000) ≤ -Real.log (345 / 512) ∧
    -Real.log (345 / 512) ≤ (394780209 / 1000000000) := by
  have h := checkLog_sound (w := (167 / 857)) (n := 12)
    (lo := (24673763 / 62500000)) (hi := (394780209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 345) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 345) = 1/(345 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-394780209 / 1000000000) (-24673763 / 62500000) (Real.log (345 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (140927289 / 500000000) ≤ -Real.log (5120 / 6787) ∧
    -Real.log (5120 / 6787) ≤ (281854579 / 1000000000) := by
  have h := checkLog_sound (w := (1667 / 11907)) (n := 12)
    (lo := (140927289 / 500000000)) (hi := (281854579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6787 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6787 / 5120) = 1/(5120 / 6787) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (140927289 / 500000000) (281854579 / 1000000000) (Real.log (6787 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6787 / 5120) = -Real.log (5120 / 6787) := by
    rw [show ((6787 / 5120) : ℝ) = ((5120 / 6787) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (19695551 / 50000000) ≤ -Real.log (3453 / 5120) ∧
    -Real.log (3453 / 5120) ≤ (393911021 / 1000000000) := by
  have h := checkLog_sound (w := (1667 / 8573)) (n := 12)
    (lo := (19695551 / 50000000)) (hi := (393911021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3453) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3453) = 1/(3453 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-393911021 / 1000000000) (-19695551 / 50000000) (Real.log (3453 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (8322431 / 40000000) ≤ -Real.log (125000 / 153911) ∧
    -Real.log (125000 / 153911) ≤ (26007597 / 125000000) := by
  have h := checkLog_sound (w := (28911 / 278911)) (n := 12)
    (lo := (8322431 / 40000000)) (hi := (26007597 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153911 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153911 / 125000) = 1/(125000 / 153911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (8322431 / 40000000) (26007597 / 125000000) (Real.log (153911 / 125000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (153911 / 125000) = -Real.log (125000 / 153911) := by
    rw [show ((153911 / 125000) : ℝ) = ((125000 / 153911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (263038891 / 1000000000) ≤ -Real.log (96089 / 125000) ∧
    -Real.log (96089 / 125000) ≤ (65759723 / 250000000) := by
  have h := checkLog_sound (w := (28911 / 221089)) (n := 12)
    (lo := (263038891 / 1000000000)) (hi := (65759723 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 96089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 96089) = 1/(96089 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-65759723 / 250000000) (-263038891 / 1000000000) (Real.log (96089 / 125000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (41680527 / 200000000) ≤ -Real.log (1000000 / 1231709) ∧
    -Real.log (1000000 / 1231709) ≤ (52100659 / 250000000) := by
  have h := checkLog_sound (w := (231709 / 2231709)) (n := 12)
    (lo := (41680527 / 200000000)) (hi := (52100659 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1231709 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1231709 / 1000000) = 1/(1000000 / 1231709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (41680527 / 200000000) (52100659 / 250000000) (Real.log (1231709 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1231709 / 1000000) = -Real.log (1000000 / 1231709) := by
    rw [show ((1231709 / 1000000) : ℝ) = ((1000000 / 1231709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (263586711 / 1000000000) ≤ -Real.log (768291 / 1000000) ∧
    -Real.log (768291 / 1000000) ≤ (32948339 / 125000000) := by
  have h := checkLog_sound (w := (231709 / 1768291)) (n := 12)
    (lo := (263586711 / 1000000000)) (hi := (32948339 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 768291) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 768291) = 1/(768291 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-32948339 / 125000000) (-263586711 / 1000000000) (Real.log (768291 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (9598961 / 62500000) ≤ -Real.log (200000 / 233201) ∧
    -Real.log (200000 / 233201) ≤ (153583377 / 1000000000) := by
  have h := checkLog_sound (w := (33201 / 433201)) (n := 12)
    (lo := (9598961 / 62500000)) (hi := (153583377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((233201 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(233201 / 200000) = 1/(200000 / 233201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (9598961 / 62500000) (153583377 / 1000000000) (Real.log (233201 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (233201 / 200000) = -Real.log (200000 / 233201) := by
    rw [show ((233201 / 200000) : ℝ) = ((200000 / 233201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (181527871 / 1000000000) ≤ -Real.log (166799 / 200000) ∧
    -Real.log (166799 / 200000) ≤ (2836373 / 15625000) := by
  have h := checkLog_sound (w := (33201 / 366799)) (n := 12)
    (lo := (181527871 / 1000000000)) (hi := (2836373 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 166799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 166799) = 1/(166799 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-2836373 / 15625000) (-181527871 / 1000000000) (Real.log (166799 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (3846273 / 25000000) ≤ -Real.log (1000000 / 1166317) ∧
    -Real.log (1000000 / 1166317) ≤ (153850921 / 1000000000) := by
  have h := checkLog_sound (w := (166317 / 2166317)) (n := 12)
    (lo := (3846273 / 25000000)) (hi := (153850921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1166317 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1166317 / 1000000) = 1/(1000000 / 1166317) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (3846273 / 25000000) (153850921 / 1000000000) (Real.log (1166317 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1166317 / 1000000) = -Real.log (1000000 / 1166317) := by
    rw [show ((1166317 / 1000000) : ℝ) = ((1000000 / 1166317) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (45475511 / 250000000) ≤ -Real.log (833683 / 1000000) ∧
    -Real.log (833683 / 1000000) ≤ (36380409 / 200000000) := by
  have h := checkLog_sound (w := (166317 / 1833683)) (n := 12)
    (lo := (45475511 / 250000000)) (hi := (36380409 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 833683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 833683) = 1/(833683 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-36380409 / 200000000) (-45475511 / 250000000) (Real.log (833683 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (675765599 / 1000000000) ≤ -Real.log (15625000000 / 30711518969) ∧
    -Real.log (15625000000 / 30711518969) ≤ (844707 / 1250000) := by
  have h := checkLog_sound (w := (15086518969 / 46336518969)) (n := 12)
    (lo := (675765599 / 1000000000)) (hi := (844707 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30711518969 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30711518969 / 15625000000) = 1/(15625000000 / 30711518969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (675765599 / 1000000000) (844707 / 1250000) (Real.log (30711518969 / 15625000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (30711518969 / 15625000000) = -Real.log (15625000000 / 30711518969) := by
    rw [show ((30711518969 / 15625000000) : ℝ) = ((15625000000 / 30711518969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (67707671 / 100000000) ≤ -Real.log (100000000000 / 196811594203) ∧
    -Real.log (100000000000 / 196811594203) ≤ (677076711 / 1000000000) := by
  have h := checkLog_sound (w := (96811594203 / 296811594203)) (n := 12)
    (lo := (67707671 / 100000000)) (hi := (677076711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((196811594203 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(196811594203 / 100000000000) = 1/(100000000000 / 196811594203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (67707671 / 100000000) (677076711 / 1000000000) (Real.log (196811594203 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (196811594203 / 100000000000) = -Real.log (100000000000 / 196811594203) := by
    rw [show ((196811594203 / 100000000000) : ℝ) = ((100000000000 / 196811594203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (471099667 / 1000000000) ≤ -Real.log (250000000000 / 400438655829) ∧
    -Real.log (250000000000 / 400438655829) ≤ (117774917 / 250000000) := by
  have h := checkLog_sound (w := (150438655829 / 650438655829)) (n := 12)
    (lo := (471099667 / 1000000000)) (hi := (117774917 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400438655829 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400438655829 / 250000000000) = 1/(250000000000 / 400438655829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (471099667 / 1000000000) (117774917 / 250000000) (Real.log (400438655829 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (400438655829 / 250000000000) = -Real.log (250000000000 / 400438655829) := by
    rw [show ((400438655829 / 250000000000) : ℝ) = ((250000000000 / 400438655829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (471989347 / 1000000000) ≤ -Real.log (50000000000 / 80159015269) ∧
    -Real.log (50000000000 / 80159015269) ≤ (117997337 / 250000000) := by
  have h := checkLog_sound (w := (30159015269 / 130159015269)) (n := 12)
    (lo := (471989347 / 1000000000)) (hi := (117997337 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80159015269 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80159015269 / 50000000000) = 1/(50000000000 / 80159015269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (471989347 / 1000000000) (117997337 / 250000000) (Real.log (80159015269 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (80159015269 / 50000000000) = -Real.log (50000000000 / 80159015269) := by
    rw [show ((80159015269 / 50000000000) : ℝ) = ((50000000000 / 80159015269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (335111247 / 1000000000) ≤ -Real.log (250000000000 / 349523977961) ∧
    -Real.log (250000000000 / 349523977961) ≤ (20944453 / 62500000) := by
  have h := checkLog_sound (w := (99523977961 / 599523977961)) (n := 12)
    (lo := (335111247 / 1000000000)) (hi := (20944453 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349523977961 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(349523977961 / 250000000000) = 1/(250000000000 / 349523977961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (335111247 / 1000000000) (20944453 / 62500000) (Real.log (349523977961 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (349523977961 / 250000000000) = -Real.log (250000000000 / 349523977961) := by
    rw [show ((349523977961 / 250000000000) : ℝ) = ((250000000000 / 349523977961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (67150593 / 200000000) ≤ -Real.log (500000000000 / 699496691189) ∧
    -Real.log (500000000000 / 699496691189) ≤ (167876483 / 500000000) := by
  have h := checkLog_sound (w := (199496691189 / 1199496691189)) (n := 12)
    (lo := (67150593 / 200000000)) (hi := (167876483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699496691189 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699496691189 / 500000000000) = 1/(500000000000 / 699496691189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (67150593 / 200000000) (167876483 / 500000000) (Real.log (699496691189 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (699496691189 / 500000000000) = -Real.log (500000000000 / 699496691189) := by
    rw [show ((699496691189 / 500000000000) : ℝ) = ((500000000000 / 699496691189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (7012781 / 250000000) ≤ -Real.log (972338655511 / 1000000000000) ∧
    -Real.log (972338655511 / 1000000000000) ≤ (224409 / 8000000) := by
  have h := checkLog_sound (w := (27661344489 / 1972338655511)) (n := 12)
    (lo := (7012781 / 250000000)) (hi := (224409 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 972338655511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 972338655511) = 1/(972338655511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-224409 / 8000000) (-7012781 / 250000000) (Real.log (972338655511 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (5588899 / 200000000) ≤ -Real.log (38897693599 / 40000000000) ∧
    -Real.log (38897693599 / 40000000000) ≤ (1746531 / 62500000) := by
  have h := checkLog_sound (w := (1102306401 / 78897693599)) (n := 12)
    (lo := (5588899 / 200000000)) (hi := (1746531 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38897693599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38897693599) = 1/(38897693599 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1746531 / 62500000) (-5588899 / 200000000) (Real.log (38897693599 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell129
