import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0121
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

theorem reflection_log_1_neg : (157804389 / 500000000) ≤ -Real.log (256 / 351) ∧
    -Real.log (256 / 351) ≤ (315608779 / 1000000000) := by
  have h := checkLog_sound (w := (95 / 607)) (n := 12)
    (lo := (157804389 / 500000000)) (hi := (315608779 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((351 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(351 / 256) = 1/(256 / 351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (157804389 / 500000000) (315608779 / 1000000000) (Real.log (351 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (351 / 256) = -Real.log (256 / 351) := by
    rw [show ((351 / 256) : ℝ) = ((256 / 351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (463773079 / 1000000000) ≤ -Real.log (161 / 256) ∧
    -Real.log (161 / 256) ≤ (11594327 / 25000000) := by
  have h := checkLog_sound (w := (95 / 417)) (n := 12)
    (lo := (463773079 / 1000000000)) (hi := (11594327 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 161) = 1/(161 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-11594327 / 25000000) (-463773079 / 1000000000) (Real.log (161 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (19672107 / 62500000) ≤ -Real.log (2560 / 3507) ∧
    -Real.log (2560 / 3507) ≤ (314753713 / 1000000000) := by
  have h := checkLog_sound (w := (947 / 6067)) (n := 12)
    (lo := (19672107 / 62500000)) (hi := (314753713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3507 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3507 / 2560) = 1/(2560 / 3507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (19672107 / 62500000) (314753713 / 1000000000) (Real.log (3507 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3507 / 2560) = -Real.log (2560 / 3507) := by
    rw [show ((3507 / 2560) : ℝ) = ((2560 / 3507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (461911459 / 1000000000) ≤ -Real.log (1613 / 2560) ∧
    -Real.log (1613 / 2560) ≤ (23095573 / 50000000) := by
  have h := checkLog_sound (w := (947 / 4173)) (n := 12)
    (lo := (461911459 / 1000000000)) (hi := (23095573 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1613) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1613) = 1/(1613 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-23095573 / 50000000) (-461911459 / 1000000000) (Real.log (1613 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (555141507 / 1000000000) ≤ -Real.log (128 / 223) ∧
    -Real.log (128 / 223) ≤ (138785377 / 250000000) := by
  have h := checkLog_sound (w := (95 / 351)) (n := 12)
    (lo := (555141507 / 1000000000)) (hi := (138785377 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((223 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(223 / 128) = 1/(128 / 223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (555141507 / 1000000000) (138785377 / 250000000) (Real.log (223 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (223 / 128) = -Real.log (128 / 223) := by
    rw [show ((223 / 128) : ℝ) = ((128 / 223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1355522701 / 1000000000) ≤ -Real.log (33 / 128) ∧
    -Real.log (33 / 128) ≤ (1355522703 / 1000000000) := by
  have h := checkLog_sound (w := (31 / 97)) (n := 12)
    (lo := (662375521 / 1000000000)) (hi := (331187761 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((64 / 33) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(64 / 33) = 1/(33 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1355522703 / 1000000000) (-1355522701 / 1000000000) (Real.log (33 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (55379531 / 100000000) ≤ -Real.log (1280 / 2227) ∧
    -Real.log (1280 / 2227) ≤ (553795311 / 1000000000) := by
  have h := checkLog_sound (w := (947 / 3507)) (n := 12)
    (lo := (55379531 / 100000000)) (hi := (553795311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2227 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2227 / 1280) = 1/(1280 / 2227) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (55379531 / 100000000) (553795311 / 1000000000) (Real.log (2227 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2227 / 1280) = -Real.log (1280 / 2227) := by
    rw [show ((2227 / 1280) : ℝ) = ((1280 / 2227) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (673236433 / 500000000) ≤ -Real.log (333 / 1280) ∧
    -Real.log (333 / 1280) ≤ (336618217 / 250000000) := by
  have h := checkLog_sound (w := (307 / 973)) (n := 12)
    (lo := (326662843 / 500000000)) (hi := (653325687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 333) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(640 / 333) = 1/(333 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-336618217 / 250000000) (-673236433 / 500000000) (Real.log (333 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (431174439 / 1000000000) ≤ -Real.log (125000 / 192383) ∧
    -Real.log (125000 / 192383) ≤ (10779361 / 25000000) := by
  have h := checkLog_sound (w := (67383 / 317383)) (n := 12)
    (lo := (431174439 / 1000000000)) (hi := (10779361 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((192383 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(192383 / 125000) = 1/(125000 / 192383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (431174439 / 1000000000) (10779361 / 25000000) (Real.log (192383 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (192383 / 125000) = -Real.log (125000 / 192383) := by
    rw [show ((192383 / 125000) : ℝ) = ((125000 / 192383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (774496073 / 1000000000) ≤ -Real.log (57617 / 125000) ∧
    -Real.log (57617 / 125000) ≤ (30979843 / 40000000) := by
  have h := checkLog_sound (w := (4883 / 120117)) (n := 12)
    (lo := (81348893 / 1000000000)) (hi := (40674447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57617) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 57617) = 1/(57617 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-30979843 / 40000000) (-774496073 / 1000000000) (Real.log (57617 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (432375097 / 1000000000) ≤ -Real.log (1000000 / 1540913) ∧
    -Real.log (1000000 / 1540913) ≤ (216187549 / 500000000) := by
  have h := checkLog_sound (w := (540913 / 2540913)) (n := 12)
    (lo := (432375097 / 1000000000)) (hi := (216187549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1540913 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1540913 / 1000000) = 1/(1000000 / 1540913) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (432375097 / 1000000000) (216187549 / 500000000) (Real.log (1540913 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1540913 / 1000000) = -Real.log (1000000 / 1540913) := by
    rw [show ((1540913 / 1000000) : ℝ) = ((1000000 / 1540913) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (778515543 / 1000000000) ≤ -Real.log (459087 / 1000000) ∧
    -Real.log (459087 / 1000000) ≤ (155703109 / 200000000) := by
  have h := checkLog_sound (w := (40913 / 959087)) (n := 12)
    (lo := (85368363 / 1000000000)) (hi := (21342091 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 459087) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 459087) = 1/(459087 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-155703109 / 200000000) (-778515543 / 1000000000) (Real.log (459087 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (69332881 / 200000000) ≤ -Real.log (500000 / 707171) ∧
    -Real.log (500000 / 707171) ≤ (173332203 / 500000000) := by
  have h := checkLog_sound (w := (207171 / 1207171)) (n := 12)
    (lo := (69332881 / 200000000)) (hi := (173332203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((707171 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(707171 / 500000) = 1/(500000 / 707171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (69332881 / 200000000) (173332203 / 500000000) (Real.log (707171 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (707171 / 500000) = -Real.log (500000 / 707171) := by
    rw [show ((707171 / 500000) : ℝ) = ((500000 / 707171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (535019277 / 1000000000) ≤ -Real.log (292829 / 500000) ∧
    -Real.log (292829 / 500000) ≤ (267509639 / 500000000) := by
  have h := checkLog_sound (w := (207171 / 792829)) (n := 12)
    (lo := (535019277 / 1000000000)) (hi := (267509639 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 292829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 292829) = 1/(292829 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-267509639 / 500000000) (-535019277 / 1000000000) (Real.log (292829 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (347842351 / 1000000000) ≤ -Real.log (1000000 / 1416009) ∧
    -Real.log (1000000 / 1416009) ≤ (21740147 / 62500000) := by
  have h := checkLog_sound (w := (416009 / 2416009)) (n := 12)
    (lo := (347842351 / 1000000000)) (hi := (21740147 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1416009 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1416009 / 1000000) = 1/(1000000 / 1416009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (347842351 / 1000000000) (21740147 / 62500000) (Real.log (1416009 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1416009 / 1000000) = -Real.log (1000000 / 1416009) := by
    rw [show ((1416009 / 1000000) : ℝ) = ((1000000 / 1416009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (537869707 / 1000000000) ≤ -Real.log (583991 / 1000000) ∧
    -Real.log (583991 / 1000000) ≤ (134467427 / 250000000) := by
  have h := checkLog_sound (w := (416009 / 1583991)) (n := 12)
    (lo := (537869707 / 1000000000)) (hi := (134467427 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 583991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 583991) = 1/(583991 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-134467427 / 250000000) (-537869707 / 1000000000) (Real.log (583991 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1205670513 / 1000000000) ≤ -Real.log (250000000000 / 834749292743) ∧
    -Real.log (250000000000 / 834749292743) ≤ (241134103 / 200000000) := by
  have h := checkLog_sound (w := (334749292743 / 1334749292743)) (n := 12)
    (lo := (512523333 / 1000000000)) (hi := (256261667 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((834749292743 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(834749292743 / 500000000000) = 1/(250000000000 / 834749292743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1205670513 / 1000000000) (241134103 / 200000000) (Real.log (834749292743 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (834749292743 / 250000000000) = -Real.log (250000000000 / 834749292743) := by
    rw [show ((834749292743 / 250000000000) : ℝ) = ((250000000000 / 834749292743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1210890641 / 1000000000) ≤ -Real.log (250000000000 / 839118184571) ∧
    -Real.log (250000000000 / 839118184571) ≤ (1210890643 / 1000000000) := by
  have h := checkLog_sound (w := (339118184571 / 1339118184571)) (n := 12)
    (lo := (517743461 / 1000000000)) (hi := (258871731 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((839118184571 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(839118184571 / 500000000000) = 1/(250000000000 / 839118184571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1210890641 / 1000000000) (1210890643 / 1000000000) (Real.log (839118184571 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (839118184571 / 250000000000) = -Real.log (250000000000 / 839118184571) := by
    rw [show ((839118184571 / 250000000000) : ℝ) = ((250000000000 / 839118184571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (440841841 / 500000000) ≤ -Real.log (100000000000 / 241496231589) ∧
    -Real.log (100000000000 / 241496231589) ≤ (220420921 / 250000000) := by
  have h := checkLog_sound (w := (41496231589 / 441496231589)) (n := 12)
    (lo := (94268251 / 500000000)) (hi := (188536503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((241496231589 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(241496231589 / 200000000000) = 1/(100000000000 / 241496231589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (440841841 / 500000000) (220420921 / 250000000) (Real.log (241496231589 / 100000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (241496231589 / 100000000000) = -Real.log (100000000000 / 241496231589) := by
    rw [show ((241496231589 / 100000000000) : ℝ) = ((100000000000 / 241496231589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (885712057 / 1000000000) ≤ -Real.log (500000000000 / 1212355156159) ∧
    -Real.log (500000000000 / 1212355156159) ≤ (885712059 / 1000000000) := by
  have h := checkLog_sound (w := (212355156159 / 2212355156159)) (n := 12)
    (lo := (192564877 / 1000000000)) (hi := (96282439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1212355156159 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1212355156159 / 1000000000000) = 1/(500000000000 / 1212355156159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (885712057 / 1000000000) (885712059 / 1000000000) (Real.log (1212355156159 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1212355156159 / 500000000000) = -Real.log (500000000000 / 1212355156159) := by
    rw [show ((1212355156159 / 500000000000) : ℝ) = ((500000000000 / 1212355156159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0121
