import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0312
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

theorem reflection_log_1_neg : (44222047 / 200000000) ≤ -Real.log (5120 / 6387) ∧
    -Real.log (5120 / 6387) ≤ (55277559 / 250000000) := by
  have h := checkLog_sound (w := (1267 / 11507)) (n := 12)
    (lo := (44222047 / 200000000)) (hi := (55277559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6387 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6387 / 5120) = 1/(5120 / 6387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (44222047 / 200000000) (55277559 / 250000000) (Real.log (6387 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6387 / 5120) = -Real.log (5120 / 6387) := by
    rw [show ((6387 / 5120) : ℝ) = ((5120 / 6387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (284302373 / 1000000000) ≤ -Real.log (3853 / 5120) ∧
    -Real.log (3853 / 5120) ≤ (142151187 / 500000000) := by
  have h := checkLog_sound (w := (1267 / 8973)) (n := 12)
    (lo := (284302373 / 1000000000)) (hi := (142151187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3853) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3853) = 1/(3853 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-142151187 / 500000000) (-284302373 / 1000000000) (Real.log (3853 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (44175071 / 200000000) ≤ -Real.log (10240 / 12771) ∧
    -Real.log (10240 / 12771) ≤ (55218839 / 250000000) := by
  have h := checkLog_sound (w := (2531 / 23011)) (n := 12)
    (lo := (44175071 / 200000000)) (hi := (55218839 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12771 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12771 / 10240) = 1/(10240 / 12771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (44175071 / 200000000) (55218839 / 250000000) (Real.log (12771 / 10240)) := by
  have h := reflection_log_3_neg
  have he : Real.log (12771 / 10240) = -Real.log (10240 / 12771) := by
    rw [show ((12771 / 10240) : ℝ) = ((10240 / 12771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (141956571 / 500000000) ≤ -Real.log (7709 / 10240) ∧
    -Real.log (7709 / 10240) ≤ (283913143 / 1000000000) := by
  have h := checkLog_sound (w := (2531 / 17949)) (n := 12)
    (lo := (141956571 / 500000000)) (hi := (283913143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7709) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7709) = 1/(7709 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-283913143 / 1000000000) (-141956571 / 500000000) (Real.log (7709 / 10240)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (402073947 / 1000000000) ≤ -Real.log (2560 / 3827) ∧
    -Real.log (2560 / 3827) ≤ (100518487 / 250000000) := by
  have h := checkLog_sound (w := (1267 / 6387)) (n := 12)
    (lo := (402073947 / 1000000000)) (hi := (100518487 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3827 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3827 / 2560) = 1/(2560 / 3827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (402073947 / 1000000000) (100518487 / 250000000) (Real.log (3827 / 2560)) := by
  have h := reflection_log_5_neg
  have he : Real.log (3827 / 2560) = -Real.log (2560 / 3827) := by
    rw [show ((3827 / 2560) : ℝ) = ((2560 / 3827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (341521079 / 500000000) ≤ -Real.log (1293 / 2560) ∧
    -Real.log (1293 / 2560) ≤ (683042159 / 1000000000) := by
  have h := checkLog_sound (w := (1267 / 3853)) (n := 12)
    (lo := (341521079 / 500000000)) (hi := (683042159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1293) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1293) = 1/(1293 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-683042159 / 1000000000) (-341521079 / 500000000) (Real.log (1293 / 2560)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (401681919 / 1000000000) ≤ -Real.log (5120 / 7651) ∧
    -Real.log (5120 / 7651) ≤ (156907 / 390625) := by
  have h := checkLog_sound (w := (2531 / 12771)) (n := 12)
    (lo := (401681919 / 1000000000)) (hi := (156907 / 390625))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7651 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7651 / 5120) = 1/(5120 / 7651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (401681919 / 1000000000) (156907 / 390625) (Real.log (7651 / 5120)) := by
  have h := reflection_log_7_neg
  have he : Real.log (7651 / 5120) = -Real.log (5120 / 7651) := by
    rw [show ((7651 / 5120) : ℝ) = ((5120 / 7651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (340941369 / 500000000) ≤ -Real.log (2589 / 5120) ∧
    -Real.log (2589 / 5120) ≤ (681882739 / 1000000000) := by
  have h := checkLog_sound (w := (2531 / 7709)) (n := 12)
    (lo := (340941369 / 500000000)) (hi := (681882739 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 2589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 2589) = 1/(2589 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-681882739 / 1000000000) (-340941369 / 500000000) (Real.log (2589 / 5120)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (151355411 / 500000000) ≤ -Real.log (1000000 / 1353523) ∧
    -Real.log (1000000 / 1353523) ≤ (302710823 / 1000000000) := by
  have h := checkLog_sound (w := (353523 / 2353523)) (n := 12)
    (lo := (151355411 / 500000000)) (hi := (302710823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1353523 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1353523 / 1000000) = 1/(1000000 / 1353523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (151355411 / 500000000) (302710823 / 1000000000) (Real.log (1353523 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1353523 / 1000000) = -Real.log (1000000 / 1353523) := by
    rw [show ((1353523 / 1000000) : ℝ) = ((1000000 / 1353523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (436217657 / 1000000000) ≤ -Real.log (646477 / 1000000) ∧
    -Real.log (646477 / 1000000) ≤ (218108829 / 500000000) := by
  have h := checkLog_sound (w := (353523 / 1646477)) (n := 12)
    (lo := (436217657 / 1000000000)) (hi := (218108829 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 646477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 646477) = 1/(646477 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-218108829 / 500000000) (-436217657 / 1000000000) (Real.log (646477 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (757573 / 2500000) ≤ -Real.log (500000 / 676977) ∧
    -Real.log (500000 / 676977) ≤ (303029201 / 1000000000) := by
  have h := checkLog_sound (w := (176977 / 1176977)) (n := 12)
    (lo := (757573 / 2500000)) (hi := (303029201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((676977 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(676977 / 500000) = 1/(500000 / 676977) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (757573 / 2500000) (303029201 / 1000000000) (Real.log (676977 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (676977 / 500000) = -Real.log (500000 / 676977) := by
    rw [show ((676977 / 500000) : ℝ) = ((500000 / 676977) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (43688457 / 100000000) ≤ -Real.log (323023 / 500000) ∧
    -Real.log (323023 / 500000) ≤ (436884571 / 1000000000) := by
  have h := checkLog_sound (w := (176977 / 823023)) (n := 12)
    (lo := (43688457 / 100000000)) (hi := (436884571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 323023) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 323023) = 1/(323023 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-436884571 / 1000000000) (-43688457 / 100000000) (Real.log (323023 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (115131871 / 500000000) ≤ -Real.log (250000 / 314733) ∧
    -Real.log (250000 / 314733) ≤ (230263743 / 1000000000) := by
  have h := checkLog_sound (w := (64733 / 564733)) (n := 12)
    (lo := (115131871 / 500000000)) (hi := (230263743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((314733 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(314733 / 250000) = 1/(250000 / 314733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (115131871 / 500000000) (230263743 / 1000000000) (Real.log (314733 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (314733 / 250000) = -Real.log (250000 / 314733) := by
    rw [show ((314733 / 250000) : ℝ) = ((250000 / 314733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (29966289 / 100000000) ≤ -Real.log (185267 / 250000) ∧
    -Real.log (185267 / 250000) ≤ (299662891 / 1000000000) := by
  have h := checkLog_sound (w := (64733 / 435267)) (n := 12)
    (lo := (29966289 / 100000000)) (hi := (299662891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 185267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 185267) = 1/(185267 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-299662891 / 1000000000) (-29966289 / 100000000) (Real.log (185267 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (230532187 / 1000000000) ≤ -Real.log (100000 / 125927) ∧
    -Real.log (100000 / 125927) ≤ (57633047 / 250000000) := by
  have h := checkLog_sound (w := (25927 / 225927)) (n := 12)
    (lo := (230532187 / 1000000000)) (hi := (57633047 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125927 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125927 / 100000) = 1/(100000 / 125927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (230532187 / 1000000000) (57633047 / 250000000) (Real.log (125927 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (125927 / 100000) = -Real.log (100000 / 125927) := by
    rw [show ((125927 / 100000) : ℝ) = ((100000 / 125927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (75029773 / 250000000) ≤ -Real.log (74073 / 100000) ∧
    -Real.log (74073 / 100000) ≤ (300119093 / 1000000000) := by
  have h := checkLog_sound (w := (25927 / 174073)) (n := 12)
    (lo := (75029773 / 250000000)) (hi := (300119093 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 74073) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 74073) = 1/(74073 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-300119093 / 1000000000) (-75029773 / 250000000) (Real.log (74073 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (738928479 / 1000000000) ≤ -Real.log (2000000000 / 4187381763) ∧
    -Real.log (2000000000 / 4187381763) ≤ (738928481 / 1000000000) := by
  have h := checkLog_sound (w := (187381763 / 8187381763)) (n := 12)
    (lo := (45781299 / 1000000000)) (hi := (457813 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4187381763 / 4000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(4187381763 / 4000000000) = 1/(2000000000 / 4187381763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (738928479 / 1000000000) (738928481 / 1000000000) (Real.log (4187381763 / 2000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4187381763 / 2000000000) = -Real.log (2000000000 / 4187381763) := by
    rw [show ((4187381763 / 2000000000) : ℝ) = ((2000000000 / 4187381763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (73991377 / 100000000) ≤ -Real.log (31250000000 / 65492337233) ∧
    -Real.log (31250000000 / 65492337233) ≤ (184978443 / 250000000) := by
  have h := checkLog_sound (w := (2992337233 / 127992337233)) (n := 12)
    (lo := (4676659 / 100000000)) (hi := (46766591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65492337233 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(65492337233 / 62500000000) = 1/(31250000000 / 65492337233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (73991377 / 100000000) (184978443 / 250000000) (Real.log (65492337233 / 31250000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (65492337233 / 31250000000) = -Real.log (31250000000 / 65492337233) := by
    rw [show ((65492337233 / 31250000000) : ℝ) = ((31250000000 / 65492337233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (66240829 / 125000000) ≤ -Real.log (250000000000 / 424701916693) ∧
    -Real.log (250000000000 / 424701916693) ≤ (529926633 / 1000000000) := by
  have h := checkLog_sound (w := (174701916693 / 674701916693)) (n := 12)
    (lo := (66240829 / 125000000)) (hi := (529926633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((424701916693 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(424701916693 / 250000000000) = 1/(250000000000 / 424701916693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (66240829 / 125000000) (529926633 / 1000000000) (Real.log (424701916693 / 250000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (424701916693 / 250000000000) = -Real.log (250000000000 / 424701916693) := by
    rw [show ((424701916693 / 250000000000) : ℝ) = ((250000000000 / 424701916693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (6633141 / 12500000) ≤ -Real.log (125000000000 / 212504893821) ∧
    -Real.log (125000000000 / 212504893821) ≤ (530651281 / 1000000000) := by
  have h := checkLog_sound (w := (87504893821 / 337504893821)) (n := 12)
    (lo := (6633141 / 12500000)) (hi := (530651281 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((212504893821 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(212504893821 / 125000000000) = 1/(125000000000 / 212504893821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (6633141 / 12500000) (530651281 / 1000000000) (Real.log (212504893821 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (212504893821 / 125000000000) = -Real.log (125000000000 / 212504893821) := by
    rw [show ((212504893821 / 125000000000) : ℝ) = ((125000000000 / 212504893821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0312
