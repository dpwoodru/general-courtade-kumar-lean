import GeneralCK.PureGapDoubleCapBiasChecker
namespace GeneralCK.Certificates.DoubleCapLowMiddle.Cell0155
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

theorem reflection_log_1_neg : (649554423 / 1000000000) ≤ -Real.log (3200 / 6127) ∧
    -Real.log (3200 / 6127) ≤ (81194303 / 125000000) := by
  have h := checkLog_sound (w := (2927 / 9327)) (n := 12)
    (lo := (649554423 / 1000000000)) (hi := (81194303 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6127 / 3200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6127 / 3200) = 1/(3200 / 6127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (649554423 / 1000000000) (81194303 / 125000000) (Real.log (6127 / 3200)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6127 / 3200) = -Real.log (3200 / 6127) := by
    rw [show ((6127 / 3200) : ℝ) = ((3200 / 6127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (2461434291 / 1000000000) ≤ -Real.log (273 / 3200) ∧
    -Real.log (273 / 3200) ≤ (492286859 / 200000000) := by
  have h := checkLog_sound (w := (127 / 673)) (n := 12)
    (lo := (381992751 / 1000000000)) (hi := (23874547 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 273) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(400 / 273) = 1/(273 / 3200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-492286859 / 200000000) (-2461434291 / 1000000000) (Real.log (273 / 3200)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (324389433 / 500000000) ≤ -Real.log (12800 / 24489) ∧
    -Real.log (12800 / 24489) ≤ (648778867 / 1000000000) := by
  have h := checkLog_sound (w := (11689 / 37289)) (n := 12)
    (lo := (324389433 / 500000000)) (hi := (648778867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24489 / 12800) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24489 / 12800) = 1/(12800 / 24489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (324389433 / 500000000) (648778867 / 1000000000) (Real.log (24489 / 12800)) := by
  have h := reflection_log_3_neg
  have he : Real.log (24489 / 12800) = -Real.log (12800 / 24489) := by
    rw [show ((24489 / 12800) : ℝ) = ((12800 / 24489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (1222092329 / 500000000) ≤ -Real.log (1111 / 12800) ∧
    -Real.log (1111 / 12800) ≤ (1222092331 / 500000000) := by
  have h := checkLog_sound (w := (489 / 2711)) (n := 12)
    (lo := (182371559 / 500000000)) (hi := (364743119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1111) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(1600 / 1111) = 1/(1111 / 12800) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-1222092331 / 500000000) (-1222092329 / 500000000) (Real.log (1111 / 12800)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (301987189 / 500000000) ≤ -Real.log (1600 / 2927) ∧
    -Real.log (1600 / 2927) ≤ (603974379 / 1000000000) := by
  have h := checkLog_sound (w := (1327 / 4527)) (n := 12)
    (lo := (301987189 / 500000000)) (hi := (603974379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2927 / 1600) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2927 / 1600) = 1/(1600 / 2927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (301987189 / 500000000) (603974379 / 1000000000) (Real.log (2927 / 1600)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2927 / 1600) = -Real.log (1600 / 2927) := by
    rw [show ((2927 / 1600) : ℝ) = ((1600 / 2927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1768287111 / 1000000000) ≤ -Real.log (273 / 1600) ∧
    -Real.log (273 / 1600) ≤ (884143557 / 500000000) := by
  have h := checkLog_sound (w := (127 / 673)) (n := 12)
    (lo := (381992751 / 1000000000)) (hi := (23874547 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 273) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(400 / 273) = 1/(273 / 1600) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-884143557 / 500000000) (-1768287111 / 1000000000) (Real.log (273 / 1600)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (301175119 / 500000000) ≤ -Real.log (6400 / 11689) ∧
    -Real.log (6400 / 11689) ≤ (602350239 / 1000000000) := by
  have h := checkLog_sound (w := (5289 / 18089)) (n := 12)
    (lo := (301175119 / 500000000)) (hi := (602350239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11689 / 6400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11689 / 6400) = 1/(6400 / 11689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (301175119 / 500000000) (602350239 / 1000000000) (Real.log (11689 / 6400)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11689 / 6400) = -Real.log (6400 / 11689) := by
    rw [show ((11689 / 6400) : ℝ) = ((6400 / 11689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (875518739 / 500000000) ≤ -Real.log (1111 / 6400) ∧
    -Real.log (1111 / 6400) ≤ (1751037481 / 1000000000) := by
  have h := checkLog_sound (w := (489 / 2711)) (n := 12)
    (lo := (182371559 / 500000000)) (hi := (364743119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600 / 1111) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1600 / 1111) = 1/(1111 / 6400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1751037481 / 1000000000) (-875518739 / 500000000) (Real.log (1111 / 6400)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (658818123 / 1000000000) ≤ -Real.log (1000000 / 1932507) ∧
    -Real.log (1000000 / 1932507) ≤ (164704531 / 250000000) := by
  have h := checkLog_sound (w := (932507 / 2932507)) (n := 12)
    (lo := (658818123 / 1000000000)) (hi := (164704531 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1932507 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1932507 / 1000000) = 1/(1000000 / 1932507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (658818123 / 1000000000) (164704531 / 250000000) (Real.log (1932507 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1932507 / 1000000) = -Real.log (1000000 / 1932507) := by
    rw [show ((1932507 / 1000000) : ℝ) = ((1000000 / 1932507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (673932847 / 250000000) ≤ -Real.log (67493 / 1000000) ∧
    -Real.log (67493 / 1000000) ≤ (42120803 / 15625000) := by
  have h := checkLog_sound (w := (57507 / 192493)) (n := 12)
    (lo := (77036231 / 125000000)) (hi := (616289849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 67493) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 67493) = 1/(67493 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-42120803 / 15625000) (-673932847 / 250000000) (Real.log (67493 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (1287809 / 1953125) ≤ -Real.log (1000000 / 1933551) ∧
    -Real.log (1000000 / 1933551) ≤ (659358209 / 1000000000) := by
  have h := checkLog_sound (w := (933551 / 2933551)) (n := 12)
    (lo := (1287809 / 1953125)) (hi := (659358209 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1933551 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1933551 / 1000000) = 1/(1000000 / 1933551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (1287809 / 1953125) (659358209 / 1000000000) (Real.log (1933551 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1933551 / 1000000) = -Real.log (1000000 / 1933551) := by
    rw [show ((1933551 / 1000000) : ℝ) = ((1000000 / 1933551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (2711320541 / 1000000000) ≤ -Real.log (66449 / 1000000) ∧
    -Real.log (66449 / 1000000) ≤ (542264109 / 200000000) := by
  have h := checkLog_sound (w := (58551 / 191449)) (n := 12)
    (lo := (631879001 / 1000000000)) (hi := (315939501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 66449) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(125000 / 66449) = 1/(66449 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-542264109 / 200000000) (-2711320541 / 1000000000) (Real.log (66449 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (328968507 / 500000000) ≤ -Real.log (200000 / 386161) ∧
    -Real.log (200000 / 386161) ≤ (131587403 / 200000000) := by
  have h := checkLog_sound (w := (186161 / 586161)) (n := 12)
    (lo := (328968507 / 500000000)) (hi := (131587403 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((386161 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(386161 / 200000) = 1/(200000 / 386161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (328968507 / 500000000) (131587403 / 200000000) (Real.log (386161 / 200000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (386161 / 200000) = -Real.log (200000 / 386161) := by
    rw [show ((386161 / 200000) : ℝ) = ((200000 / 386161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (2670826671 / 1000000000) ≤ -Real.log (13839 / 200000) ∧
    -Real.log (13839 / 200000) ≤ (106833067 / 40000000) := by
  have h := checkLog_sound (w := (11161 / 38839)) (n := 12)
    (lo := (591385131 / 1000000000)) (hi := (147846283 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 13839) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(25000 / 13839) = 1/(13839 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-106833067 / 40000000) (-2670826671 / 1000000000) (Real.log (13839 / 200000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (5144627 / 7812500) ≤ -Real.log (250000 / 482979) ∧
    -Real.log (250000 / 482979) ≤ (658512257 / 1000000000) := by
  have h := checkLog_sound (w := (232979 / 732979)) (n := 12)
    (lo := (5144627 / 7812500)) (hi := (658512257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((482979 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(482979 / 250000) = 1/(250000 / 482979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (5144627 / 7812500) (658512257 / 1000000000) (Real.log (482979 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (482979 / 250000) = -Real.log (250000 / 482979) := by
    rw [show ((482979 / 250000) : ℝ) = ((250000 / 482979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (33587663 / 12500000) ≤ -Real.log (17021 / 250000) ∧
    -Real.log (17021 / 250000) ≤ (671753261 / 250000000) := by
  have h := checkLog_sound (w := (14229 / 48271)) (n := 12)
    (lo := (1215143 / 2000000)) (hi := (607571501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 17021) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(31250 / 17021) = 1/(17021 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-671753261 / 250000000) (-33587663 / 12500000) (Real.log (17021 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (3354549511 / 1000000000) ≤ -Real.log (250000000000 / 7158175662661) ∧
    -Real.log (250000000000 / 7158175662661) ≤ (838637379 / 250000000) := by
  have h := checkLog_sound (w := (3158175662661 / 11158175662661)) (n := 12)
    (lo := (581960791 / 1000000000)) (hi := (72745099 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7158175662661 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(7158175662661 / 4000000000000) = 1/(250000000000 / 7158175662661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (3354549511 / 1000000000) (838637379 / 250000000) (Real.log (7158175662661 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (7158175662661 / 250000000000) = -Real.log (250000000000 / 7158175662661) := by
    rw [show ((7158175662661 / 250000000000) : ℝ) = ((250000000000 / 7158175662661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (3370678749 / 1000000000) ≤ -Real.log (50000000000 / 1454913542717) ∧
    -Real.log (50000000000 / 1454913542717) ≤ (1685339377 / 500000000) := by
  have h := checkLog_sound (w := (654913542717 / 2254913542717)) (n := 12)
    (lo := (598090029 / 1000000000)) (hi := (59809003 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1454913542717 / 800000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(1454913542717 / 800000000000) = 1/(50000000000 / 1454913542717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (3370678749 / 1000000000) (1685339377 / 500000000) (Real.log (1454913542717 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1454913542717 / 50000000000) = -Real.log (50000000000 / 1454913542717) := by
    rw [show ((1454913542717 / 50000000000) : ℝ) = ((50000000000 / 1454913542717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (665752737 / 200000000) ≤ -Real.log (31250000000 / 871994454079) ∧
    -Real.log (31250000000 / 871994454079) ≤ (332876369 / 100000000) := by
  have h := checkLog_sound (w := (371994454079 / 1371994454079)) (n := 12)
    (lo := (111234993 / 200000000)) (hi := (278087483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((871994454079 / 500000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(871994454079 / 500000000000) = 1/(31250000000 / 871994454079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (665752737 / 200000000) (332876369 / 100000000) (Real.log (871994454079 / 31250000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (871994454079 / 31250000000) = -Real.log (31250000000 / 871994454079) := by
    rw [show ((871994454079 / 31250000000) : ℝ) = ((31250000000 / 871994454079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (209095331 / 62500000) ≤ -Real.log (250000000000 / 7093869337877) ∧
    -Real.log (250000000000 / 7093869337877) ≤ (3345525301 / 1000000000) := by
  have h := checkLog_sound (w := (3093869337877 / 11093869337877)) (n := 12)
    (lo := (4476067 / 7812500)) (hi := (572936577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((7093869337877 / 4000000000000) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(7093869337877 / 4000000000000) = 1/(250000000000 / 7093869337877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (209095331 / 62500000) (3345525301 / 1000000000) (Real.log (7093869337877 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (7093869337877 / 250000000000) = -Real.log (250000000000 / 7093869337877) := by
    rw [show ((7093869337877 / 250000000000) : ℝ) = ((250000000000 / 7093869337877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapLowMiddle.Cell0155
