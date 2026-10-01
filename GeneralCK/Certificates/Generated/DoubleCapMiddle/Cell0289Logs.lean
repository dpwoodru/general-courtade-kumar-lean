import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0289
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

theorem reflection_log_1_neg : (14156081 / 62500000) ≤ -Real.log (10240 / 12843) ∧
    -Real.log (10240 / 12843) ≤ (226497297 / 1000000000) := by
  have h := checkLog_sound (w := (2603 / 23083)) (n := 12)
    (lo := (14156081 / 62500000)) (hi := (226497297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12843 / 10240) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12843 / 10240) = 1/(10240 / 12843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (14156081 / 62500000) (226497297 / 1000000000) (Real.log (12843 / 10240)) := by
  have h := reflection_log_1_neg
  have he : Real.log (12843 / 10240) = -Real.log (10240 / 12843) := by
    rw [show ((12843 / 10240) : ℝ) = ((10240 / 12843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (293296763 / 1000000000) ≤ -Real.log (7637 / 10240) ∧
    -Real.log (7637 / 10240) ≤ (73324191 / 250000000) := by
  have h := checkLog_sound (w := (2603 / 17877)) (n := 12)
    (lo := (293296763 / 1000000000)) (hi := (73324191 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10240 / 7637) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10240 / 7637) = 1/(7637 / 10240) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-73324191 / 250000000) (-293296763 / 1000000000) (Real.log (7637 / 10240)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (113131839 / 500000000) ≤ -Real.log (256 / 321) ∧
    -Real.log (256 / 321) ≤ (226263679 / 1000000000) := by
  have h := checkLog_sound (w := (65 / 577)) (n := 12)
    (lo := (113131839 / 500000000)) (hi := (226263679 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((321 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(321 / 256) = 1/(256 / 321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (113131839 / 500000000) (226263679 / 1000000000) (Real.log (321 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (321 / 256) = -Real.log (256 / 321) := by
    rw [show ((321 / 256) : ℝ) = ((256 / 321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (18306501 / 62500000) ≤ -Real.log (191 / 256) ∧
    -Real.log (191 / 256) ≤ (292904017 / 1000000000) := by
  have h := checkLog_sound (w := (65 / 447)) (n := 12)
    (lo := (18306501 / 62500000)) (hi := (292904017 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 191) = 1/(191 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-292904017 / 1000000000) (-18306501 / 62500000) (Real.log (191 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (8220969 / 20000000) ≤ -Real.log (5120 / 7723) ∧
    -Real.log (5120 / 7723) ≤ (411048451 / 1000000000) := by
  have h := checkLog_sound (w := (2603 / 12843)) (n := 12)
    (lo := (8220969 / 20000000)) (hi := (411048451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7723 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(7723 / 5120) = 1/(5120 / 7723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (8220969 / 20000000) (411048451 / 1000000000) (Real.log (7723 / 5120)) := by
  have h := reflection_log_5_neg
  have he : Real.log (7723 / 5120) = -Real.log (5120 / 7723) := by
    rw [show ((7723 / 5120) : ℝ) = ((5120 / 7723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (355043361 / 500000000) ≤ -Real.log (2517 / 5120) ∧
    -Real.log (2517 / 5120) ≤ (177521681 / 250000000) := by
  have h := checkLog_sound (w := (43 / 5077)) (n := 12)
    (lo := (8469771 / 500000000)) (hi := (16939543 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 2517) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(2560 / 2517) = 1/(2517 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-177521681 / 250000000) (-355043361 / 500000000) (Real.log (2517 / 5120)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (102664981 / 250000000) ≤ -Real.log (128 / 193) ∧
    -Real.log (128 / 193) ≤ (16426397 / 40000000) := by
  have h := checkLog_sound (w := (65 / 321)) (n := 12)
    (lo := (102664981 / 250000000)) (hi := (16426397 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((193 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(193 / 128) = 1/(128 / 193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (102664981 / 250000000) (16426397 / 40000000) (Real.log (193 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (193 / 128) = -Real.log (128 / 193) := by
    rw [show ((193 / 128) : ℝ) = ((128 / 193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (44305971 / 62500000) ≤ -Real.log (63 / 128) ∧
    -Real.log (63 / 128) ≤ (354447769 / 500000000) := by
  have h := checkLog_sound (w := (1 / 127)) (n := 12)
    (lo := (3937089 / 250000000)) (hi := (15748357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 63) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 63) = 1/(63 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-354447769 / 500000000) (-44305971 / 62500000) (Real.log (63 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (61998663 / 200000000) ≤ -Real.log (125000 / 170427) ∧
    -Real.log (125000 / 170427) ≤ (77498329 / 250000000) := by
  have h := checkLog_sound (w := (45427 / 295427)) (n := 12)
    (lo := (61998663 / 200000000)) (hi := (77498329 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((170427 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(170427 / 125000) = 1/(125000 / 170427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (61998663 / 200000000) (77498329 / 250000000) (Real.log (170427 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (170427 / 125000) = -Real.log (125000 / 170427) := by
    rw [show ((170427 / 125000) : ℝ) = ((125000 / 170427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (451638897 / 1000000000) ≤ -Real.log (79573 / 125000) ∧
    -Real.log (79573 / 125000) ≤ (225819449 / 500000000) := by
  have h := checkLog_sound (w := (45427 / 204573)) (n := 12)
    (lo := (451638897 / 1000000000)) (hi := (225819449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 79573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 79573) = 1/(79573 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-225819449 / 500000000) (-451638897 / 1000000000) (Real.log (79573 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (77577529 / 250000000) ≤ -Real.log (125000 / 170481) ∧
    -Real.log (125000 / 170481) ≤ (310310117 / 1000000000) := by
  have h := checkLog_sound (w := (45481 / 295481)) (n := 12)
    (lo := (77577529 / 250000000)) (hi := (310310117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((170481 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(170481 / 125000) = 1/(125000 / 170481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (77577529 / 250000000) (310310117 / 1000000000) (Real.log (170481 / 125000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (170481 / 125000) = -Real.log (125000 / 170481) := by
    rw [show ((170481 / 125000) : ℝ) = ((125000 / 170481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1809271 / 4000000) ≤ -Real.log (79519 / 125000) ∧
    -Real.log (79519 / 125000) ≤ (452317751 / 1000000000) := by
  have h := checkLog_sound (w := (45481 / 204519)) (n := 12)
    (lo := (1809271 / 4000000)) (hi := (452317751 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 79519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 79519) = 1/(79519 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-452317751 / 1000000000) (-1809271 / 4000000) (Real.log (79519 / 125000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (236430093 / 1000000000) ≤ -Real.log (1000000 / 1266719) ∧
    -Real.log (1000000 / 1266719) ≤ (118215047 / 500000000) := by
  have h := checkLog_sound (w := (266719 / 2266719)) (n := 12)
    (lo := (236430093 / 1000000000)) (hi := (118215047 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1266719 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1266719 / 1000000) = 1/(1000000 / 1266719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (236430093 / 1000000000) (118215047 / 500000000) (Real.log (1266719 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1266719 / 1000000) = -Real.log (1000000 / 1266719) := by
    rw [show ((1266719 / 1000000) : ℝ) = ((1000000 / 1266719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (155113147 / 500000000) ≤ -Real.log (733281 / 1000000) ∧
    -Real.log (733281 / 1000000) ≤ (62045259 / 200000000) := by
  have h := checkLog_sound (w := (266719 / 1733281)) (n := 12)
    (lo := (155113147 / 500000000)) (hi := (62045259 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 733281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 733281) = 1/(733281 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-62045259 / 200000000) (-155113147 / 500000000) (Real.log (733281 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (29587407 / 125000000) ≤ -Real.log (50000 / 63353) ∧
    -Real.log (50000 / 63353) ≤ (236699257 / 1000000000) := by
  have h := checkLog_sound (w := (13353 / 113353)) (n := 12)
    (lo := (29587407 / 125000000)) (hi := (236699257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63353 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63353 / 50000) = 1/(50000 / 63353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (29587407 / 125000000) (236699257 / 1000000000) (Real.log (63353 / 50000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (63353 / 50000) = -Real.log (50000 / 63353) := by
    rw [show ((63353 / 50000) : ℝ) = ((50000 / 63353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (62138287 / 200000000) ≤ -Real.log (36647 / 50000) ∧
    -Real.log (36647 / 50000) ≤ (77672859 / 250000000) := by
  have h := checkLog_sound (w := (13353 / 86647)) (n := 12)
    (lo := (62138287 / 200000000)) (hi := (77672859 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 36647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 36647) = 1/(36647 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-77672859 / 250000000) (-62138287 / 200000000) (Real.log (36647 / 50000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (190408053 / 250000000) ≤ -Real.log (250000000000 / 535442298267) ∧
    -Real.log (250000000000 / 535442298267) ≤ (380816107 / 500000000) := by
  have h := checkLog_sound (w := (35442298267 / 1035442298267)) (n := 12)
    (lo := (8560629 / 125000000)) (hi := (68485033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((535442298267 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(535442298267 / 500000000000) = 1/(250000000000 / 535442298267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (190408053 / 250000000) (380816107 / 500000000) (Real.log (535442298267 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (535442298267 / 250000000000) = -Real.log (250000000000 / 535442298267) := by
    rw [show ((535442298267 / 250000000000) : ℝ) = ((250000000000 / 535442298267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (381313933 / 500000000) ≤ -Real.log (250000000000 / 535975678769) ∧
    -Real.log (250000000000 / 535975678769) ≤ (190656967 / 250000000) := by
  have h := checkLog_sound (w := (35975678769 / 1035975678769)) (n := 12)
    (lo := (34740343 / 500000000)) (hi := (69480687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((535975678769 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(535975678769 / 500000000000) = 1/(250000000000 / 535975678769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (381313933 / 500000000) (190656967 / 250000000) (Real.log (535975678769 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (535975678769 / 250000000000) = -Real.log (250000000000 / 535975678769) := by
    rw [show ((535975678769 / 250000000000) : ℝ) = ((250000000000 / 535975678769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (546656387 / 1000000000) ≤ -Real.log (500000000000 / 863733684631) ∧
    -Real.log (500000000000 / 863733684631) ≤ (136664097 / 250000000) := by
  have h := checkLog_sound (w := (363733684631 / 1363733684631)) (n := 12)
    (lo := (546656387 / 1000000000)) (hi := (136664097 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((863733684631 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(863733684631 / 500000000000) = 1/(500000000000 / 863733684631) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (546656387 / 1000000000) (136664097 / 250000000) (Real.log (863733684631 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (863733684631 / 500000000000) = -Real.log (500000000000 / 863733684631) := by
    rw [show ((863733684631 / 500000000000) : ℝ) = ((500000000000 / 863733684631) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (136847673 / 250000000) ≤ -Real.log (100000000000 / 172873632221) ∧
    -Real.log (100000000000 / 172873632221) ≤ (547390693 / 1000000000) := by
  have h := checkLog_sound (w := (72873632221 / 272873632221)) (n := 12)
    (lo := (136847673 / 250000000)) (hi := (547390693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172873632221 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172873632221 / 100000000000) = 1/(100000000000 / 172873632221) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (136847673 / 250000000) (547390693 / 1000000000) (Real.log (172873632221 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (172873632221 / 100000000000) = -Real.log (100000000000 / 172873632221) := by
    rw [show ((172873632221 / 100000000000) : ℝ) = ((100000000000 / 172873632221) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0289
