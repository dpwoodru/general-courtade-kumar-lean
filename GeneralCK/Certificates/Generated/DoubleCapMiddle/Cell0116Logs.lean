import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0116
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

theorem reflection_log_1_neg : (319873177 / 1000000000) ≤ -Real.log (512 / 705) ∧
    -Real.log (512 / 705) ≤ (159936589 / 500000000) := by
  have h := checkLog_sound (w := (193 / 1217)) (n := 12)
    (lo := (319873177 / 1000000000)) (hi := (159936589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((705 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(705 / 512) = 1/(512 / 705) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (319873177 / 1000000000) (159936589 / 500000000) (Real.log (705 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (705 / 512) = -Real.log (512 / 705) := by
    rw [show ((705 / 512) : ℝ) = ((512 / 705) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (236566761 / 500000000) ≤ -Real.log (319 / 512) ∧
    -Real.log (319 / 512) ≤ (473133523 / 1000000000) := by
  have h := checkLog_sound (w := (193 / 831)) (n := 12)
    (lo := (236566761 / 500000000)) (hi := (473133523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 319) = 1/(319 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-473133523 / 1000000000) (-236566761 / 500000000) (Real.log (319 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (319021751 / 1000000000) ≤ -Real.log (1280 / 1761) ∧
    -Real.log (1280 / 1761) ≤ (39877719 / 125000000) := by
  have h := checkLog_sound (w := (481 / 3041)) (n := 12)
    (lo := (319021751 / 1000000000)) (hi := (39877719 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1761 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1761 / 1280) = 1/(1280 / 1761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (319021751 / 1000000000) (39877719 / 125000000) (Real.log (1761 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1761 / 1280) = -Real.log (1280 / 1761) := by
    rw [show ((1761 / 1280) : ℝ) = ((1280 / 1761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (471254411 / 1000000000) ≤ -Real.log (799 / 1280) ∧
    -Real.log (799 / 1280) ≤ (117813603 / 250000000) := by
  have h := checkLog_sound (w := (481 / 2079)) (n := 12)
    (lo := (471254411 / 1000000000)) (hi := (117813603 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 799) = 1/(799 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-117813603 / 250000000) (-471254411 / 1000000000) (Real.log (799 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (561845443 / 1000000000) ≤ -Real.log (256 / 449) ∧
    -Real.log (256 / 449) ≤ (140461361 / 250000000) := by
  have h := checkLog_sound (w := (193 / 705)) (n := 12)
    (lo := (561845443 / 1000000000)) (hi := (140461361 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((449 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(449 / 256) = 1/(256 / 449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (561845443 / 1000000000) (140461361 / 250000000) (Real.log (449 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (449 / 256) = -Real.log (256 / 449) := by
    rw [show ((449 / 256) : ℝ) = ((256 / 449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (350510679 / 250000000) ≤ -Real.log (63 / 256) ∧
    -Real.log (63 / 256) ≤ (1402042719 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 127)) (n := 12)
    (lo := (3937089 / 250000000)) (hi := (15748357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 63) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(64 / 63) = 1/(63 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1402042719 / 1000000000) (-350510679 / 250000000) (Real.log (63 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (280254123 / 500000000) ≤ -Real.log (640 / 1121) ∧
    -Real.log (640 / 1121) ≤ (560508247 / 1000000000) := by
  have h := checkLog_sound (w := (481 / 1761)) (n := 12)
    (lo := (280254123 / 500000000)) (hi := (560508247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1121 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1121 / 640) = 1/(640 / 1121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (280254123 / 500000000) (560508247 / 1000000000) (Real.log (1121 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1121 / 640) = -Real.log (640 / 1121) := by
    rw [show ((1121 / 640) : ℝ) = ((640 / 1121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1392563973 / 1000000000) ≤ -Real.log (159 / 640) ∧
    -Real.log (159 / 640) ≤ (174070497 / 125000000) := by
  have h := checkLog_sound (w := (1 / 319)) (n := 12)
    (lo := (6269613 / 1000000000)) (hi := (3134807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 159) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(160 / 159) = 1/(159 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-174070497 / 125000000) (-1392563973 / 1000000000) (Real.log (159 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (437173701 / 1000000000) ≤ -Real.log (40000 / 61933) ∧
    -Real.log (40000 / 61933) ≤ (218586851 / 500000000) := by
  have h := checkLog_sound (w := (21933 / 101933)) (n := 12)
    (lo := (437173701 / 1000000000)) (hi := (218586851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61933 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61933 / 40000) = 1/(40000 / 61933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (437173701 / 1000000000) (218586851 / 500000000) (Real.log (61933 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (61933 / 40000) = -Real.log (40000 / 61933) := by
    rw [show ((61933 / 40000) : ℝ) = ((40000 / 61933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (794792383 / 1000000000) ≤ -Real.log (18067 / 40000) ∧
    -Real.log (18067 / 40000) ≤ (158958477 / 200000000) := by
  have h := checkLog_sound (w := (1933 / 38067)) (n := 12)
    (lo := (101645203 / 1000000000)) (hi := (25411301 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 18067) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 18067) = 1/(18067 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-158958477 / 200000000) (-794792383 / 1000000000) (Real.log (18067 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (219187139 / 500000000) ≤ -Real.log (200000 / 310037) ∧
    -Real.log (200000 / 310037) ≤ (438374279 / 1000000000) := by
  have h := checkLog_sound (w := (110037 / 510037)) (n := 12)
    (lo := (219187139 / 500000000)) (hi := (438374279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((310037 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(310037 / 200000) = 1/(200000 / 310037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (219187139 / 500000000) (438374279 / 1000000000) (Real.log (310037 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (310037 / 200000) = -Real.log (200000 / 310037) := by
    rw [show ((310037 / 200000) : ℝ) = ((200000 / 310037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (798918891 / 1000000000) ≤ -Real.log (89963 / 200000) ∧
    -Real.log (89963 / 200000) ≤ (798918893 / 1000000000) := by
  have h := checkLog_sound (w := (10037 / 189963)) (n := 12)
    (lo := (105771711 / 1000000000)) (hi := (1652683 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 89963) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 89963) = 1/(89963 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-798918893 / 1000000000) (-798918891 / 1000000000) (Real.log (89963 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (2203579 / 6250000) ≤ -Real.log (1000000 / 1422723) ∧
    -Real.log (1000000 / 1422723) ≤ (352572641 / 1000000000) := by
  have h := checkLog_sound (w := (422723 / 2422723)) (n := 12)
    (lo := (2203579 / 6250000)) (hi := (352572641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1422723 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1422723 / 1000000) = 1/(1000000 / 1422723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (2203579 / 6250000) (352572641 / 1000000000) (Real.log (1422723 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1422723 / 1000000) = -Real.log (1000000 / 1422723) := by
    rw [show ((1422723 / 1000000) : ℝ) = ((1000000 / 1422723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (274716529 / 500000000) ≤ -Real.log (577277 / 1000000) ∧
    -Real.log (577277 / 1000000) ≤ (549433059 / 1000000000) := by
  have h := checkLog_sound (w := (422723 / 1577277)) (n := 12)
    (lo := (274716529 / 500000000)) (hi := (549433059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 577277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 577277) = 1/(577277 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-549433059 / 1000000000) (-274716529 / 500000000) (Real.log (577277 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (353760501 / 1000000000) ≤ -Real.log (500000 / 712207) ∧
    -Real.log (500000 / 712207) ≤ (176880251 / 500000000) := by
  have h := checkLog_sound (w := (212207 / 1212207)) (n := 12)
    (lo := (353760501 / 1000000000)) (hi := (176880251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((712207 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(712207 / 500000) = 1/(500000 / 712207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (353760501 / 1000000000) (176880251 / 500000000) (Real.log (712207 / 500000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (712207 / 500000) = -Real.log (500000 / 712207) := by
    rw [show ((712207 / 500000) : ℝ) = ((500000 / 712207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (276183313 / 500000000) ≤ -Real.log (287793 / 500000) ∧
    -Real.log (287793 / 500000) ≤ (552366627 / 1000000000) := by
  have h := checkLog_sound (w := (212207 / 787793)) (n := 12)
    (lo := (276183313 / 500000000)) (hi := (552366627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 287793) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 287793) = 1/(287793 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-552366627 / 1000000000) (-276183313 / 500000000) (Real.log (287793 / 500000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (246393217 / 200000000) ≤ -Real.log (250000000000 / 856990645929) ∧
    -Real.log (250000000000 / 856990645929) ≤ (1231966087 / 1000000000) := by
  have h := checkLog_sound (w := (356990645929 / 1356990645929)) (n := 12)
    (lo := (107763781 / 200000000)) (hi := (269409453 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((856990645929 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(856990645929 / 500000000000) = 1/(250000000000 / 856990645929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (246393217 / 200000000) (1231966087 / 1000000000) (Real.log (856990645929 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (856990645929 / 250000000000) = -Real.log (250000000000 / 856990645929) := by
    rw [show ((856990645929 / 250000000000) : ℝ) = ((250000000000 / 856990645929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1237293169 / 1000000000) ≤ -Real.log (500000000000 / 1723136178207) ∧
    -Real.log (500000000000 / 1723136178207) ≤ (1237293171 / 1000000000) := by
  have h := checkLog_sound (w := (723136178207 / 2723136178207)) (n := 12)
    (lo := (544145989 / 1000000000)) (hi := (54414599 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1723136178207 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1723136178207 / 1000000000000) = 1/(500000000000 / 1723136178207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1237293169 / 1000000000) (1237293171 / 1000000000) (Real.log (1723136178207 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1723136178207 / 500000000000) = -Real.log (500000000000 / 1723136178207) := by
    rw [show ((1723136178207 / 500000000000) : ℝ) = ((500000000000 / 1723136178207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (451002849 / 500000000) ≤ -Real.log (125000000000 / 308067660759) ∧
    -Real.log (125000000000 / 308067660759) ≤ (9020057 / 10000000) := by
  have h := checkLog_sound (w := (58067660759 / 558067660759)) (n := 12)
    (lo := (104429259 / 500000000)) (hi := (208858519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((308067660759 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(308067660759 / 250000000000) = 1/(125000000000 / 308067660759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (451002849 / 500000000) (9020057 / 10000000) (Real.log (308067660759 / 125000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (308067660759 / 125000000000) = -Real.log (125000000000 / 308067660759) := by
    rw [show ((308067660759 / 125000000000) : ℝ) = ((125000000000 / 308067660759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (906127127 / 1000000000) ≤ -Real.log (15625000000 / 38667494953) ∧
    -Real.log (15625000000 / 38667494953) ≤ (906127129 / 1000000000) := by
  have h := checkLog_sound (w := (7417494953 / 69917494953)) (n := 12)
    (lo := (212979947 / 1000000000)) (hi := (53244987 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38667494953 / 31250000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(38667494953 / 31250000000) = 1/(15625000000 / 38667494953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (906127127 / 1000000000) (906127129 / 1000000000) (Real.log (38667494953 / 15625000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (38667494953 / 15625000000) = -Real.log (15625000000 / 38667494953) := by
    rw [show ((38667494953 / 15625000000) : ℝ) = ((15625000000 / 38667494953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0116
