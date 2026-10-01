import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_5184_neg : (90153269 / 1000000000) ≤ -Real.log (500000 / 547171) ∧
    -Real.log (500000 / 547171) ≤ (9015327 / 100000000) := by
  have h := checkLog_sound (w := (47171 / 1047171)) (n := 12)
    (lo := (90153269 / 1000000000)) (hi := (9015327 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547171 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547171 / 500000) = 1/(500000 / 547171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5184 : Bounds (90153269 / 1000000000) (9015327 / 100000000) (Real.log (547171 / 500000)) := by
  have h := reflection_log_5184_neg
  have he : Real.log (547171 / 500000) = -Real.log (500000 / 547171) := by
    rw [show ((547171 / 500000) : ℝ) = ((500000 / 547171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5185_neg : (99093527 / 1000000000) ≤ -Real.log (452829 / 500000) ∧
    -Real.log (452829 / 500000) ≤ (12386691 / 125000000) := by
  have h := checkLog_sound (w := (47171 / 952829)) (n := 12)
    (lo := (99093527 / 1000000000)) (hi := (12386691 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452829) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 452829) = 1/(452829 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5185 : Bounds (-12386691 / 125000000) (-99093527 / 1000000000) (Real.log (452829 / 500000)) := by
  have h := reflection_log_5185_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5186_neg : (4470129 / 500000000) ≤ -Real.log (247774896759 / 250000000000) ∧
    -Real.log (247774896759 / 250000000000) ≤ (8940259 / 1000000000) := by
  have h := checkLog_sound (w := (2225103241 / 497774896759)) (n := 12)
    (lo := (4470129 / 500000000)) (hi := (8940259 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247774896759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247774896759) = 1/(247774896759 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5186 : Bounds (-8940259 / 1000000000) (-4470129 / 500000000) (Real.log (247774896759 / 250000000000)) := by
  have h := reflection_log_5186_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5187_neg : (4447503 / 500000000) ≤ -Real.log (15486631831 / 15625000000) ∧
    -Real.log (15486631831 / 15625000000) ≤ (8895007 / 1000000000) := by
  have h := checkLog_sound (w := (138368169 / 31111631831)) (n := 12)
    (lo := (4447503 / 500000000)) (hi := (8895007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15486631831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15486631831) = 1/(15486631831 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5187 : Bounds (-8895007 / 1000000000) (-4447503 / 500000000) (Real.log (15486631831 / 15625000000)) := by
  have h := reflection_log_5187_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5188_neg : (188766533 / 1000000000) ≤ -Real.log (500000000000 / 603879474023) ∧
    -Real.log (500000000000 / 603879474023) ≤ (94383267 / 500000000) := by
  have h := checkLog_sound (w := (103879474023 / 1103879474023)) (n := 12)
    (lo := (188766533 / 1000000000)) (hi := (94383267 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((603879474023 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(603879474023 / 500000000000) = 1/(500000000000 / 603879474023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5188 : Bounds (188766533 / 1000000000) (94383267 / 500000000) (Real.log (603879474023 / 500000000000)) := by
  have h := reflection_log_5188_neg
  have he : Real.log (603879474023 / 500000000000) = -Real.log (500000000000 / 603879474023) := by
    rw [show ((603879474023 / 500000000000) : ℝ) = ((500000000000 / 603879474023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5189_neg : (189246797 / 1000000000) ≤ -Real.log (62500000000 / 75521195639) ∧
    -Real.log (62500000000 / 75521195639) ≤ (94623399 / 500000000) := by
  have h := checkLog_sound (w := (13021195639 / 138021195639)) (n := 12)
    (lo := (189246797 / 1000000000)) (hi := (94623399 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((75521195639 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(75521195639 / 62500000000) = 1/(62500000000 / 75521195639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5189 : Bounds (189246797 / 1000000000) (94623399 / 500000000) (Real.log (75521195639 / 62500000000)) := by
  have h := reflection_log_5189_neg
  have he : Real.log (75521195639 / 62500000000) = -Real.log (62500000000 / 75521195639) := by
    rw [show ((75521195639 / 62500000000) : ℝ) = ((62500000000 / 75521195639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5190_neg : (75773559 / 200000000) ≤ -Real.log (500000000000 / 730314960629) ∧
    -Real.log (500000000000 / 730314960629) ≤ (94716949 / 250000000) := by
  have h := checkLog_sound (w := (230314960629 / 1230314960629)) (n := 12)
    (lo := (75773559 / 200000000)) (hi := (94716949 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((730314960629 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(730314960629 / 500000000000) = 1/(500000000000 / 730314960629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5190 : Bounds (75773559 / 200000000) (94716949 / 250000000) (Real.log (730314960629 / 500000000000)) := by
  have h := reflection_log_5190_neg
  have he : Real.log (730314960629 / 500000000000) = -Real.log (500000000000 / 730314960629) := by
    rw [show ((730314960629 / 500000000000) : ℝ) = ((500000000000 / 730314960629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5191_neg : (189537531 / 500000000) ≤ -Real.log (250000000000 / 365233173373) ∧
    -Real.log (250000000000 / 365233173373) ≤ (379075063 / 1000000000) := by
  have h := checkLog_sound (w := (115233173373 / 615233173373)) (n := 12)
    (lo := (189537531 / 500000000)) (hi := (379075063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((365233173373 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(365233173373 / 250000000000) = 1/(250000000000 / 365233173373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5191 : Bounds (189537531 / 500000000) (379075063 / 1000000000) (Real.log (365233173373 / 250000000000)) := by
  have h := reflection_log_5191_neg
  have he : Real.log (365233173373 / 250000000000) = -Real.log (250000000000 / 365233173373) := by
    rw [show ((365233173373 / 250000000000) : ℝ) = ((250000000000 / 365233173373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5192_neg : (85883021 / 500000000) ≤ -Real.log (5000 / 5937) ∧
    -Real.log (5000 / 5937) ≤ (171766043 / 1000000000) := by
  have h := checkLog_sound (w := (937 / 10937)) (n := 12)
    (lo := (85883021 / 500000000)) (hi := (171766043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5937 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5937 / 5000) = 1/(5000 / 5937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5192 : Bounds (85883021 / 500000000) (171766043 / 1000000000) (Real.log (5937 / 5000)) := by
  have h := reflection_log_5192_neg
  have he : Real.log (5937 / 5000) = -Real.log (5000 / 5937) := by
    rw [show ((5937 / 5000) : ℝ) = ((5000 / 5937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5193_neg : (41503259 / 200000000) ≤ -Real.log (4063 / 5000) ∧
    -Real.log (4063 / 5000) ≤ (25939537 / 125000000) := by
  have h := checkLog_sound (w := (937 / 9063)) (n := 12)
    (lo := (41503259 / 200000000)) (hi := (25939537 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4063) = 1/(4063 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5193 : Bounds (-25939537 / 125000000) (-41503259 / 200000000) (Real.log (4063 / 5000)) := by
  have h := reflection_log_5193_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5194_neg : (93691 / 500000000) ≤ -Real.log (5000000 / 5000937) ∧
    -Real.log (5000000 / 5000937) ≤ (187383 / 1000000000) := by
  have h := checkLog_sound (w := (937 / 10000937)) (n := 12)
    (lo := (93691 / 500000000)) (hi := (187383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000937 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000937 / 5000000) = 1/(5000000 / 5000937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5194 : Bounds (93691 / 500000000) (187383 / 1000000000) (Real.log (5000937 / 5000000)) := by
  have h := reflection_log_5194_neg
  have he : Real.log (5000937 / 5000000) = -Real.log (5000000 / 5000937) := by
    rw [show ((5000937 / 5000000) : ℝ) = ((5000000 / 5000937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5195_neg : (187417 / 1000000000) ≤ -Real.log (4999063 / 5000000) ∧
    -Real.log (4999063 / 5000000) ≤ (93709 / 500000000) := by
  have h := checkLog_sound (w := (937 / 9999063)) (n := 12)
    (lo := (187417 / 1000000000)) (hi := (93709 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999063) = 1/(4999063 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5195 : Bounds (-93709 / 500000000) (-187417 / 1000000000) (Real.log (4999063 / 5000000)) := by
  have h := reflection_log_5195_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5196_neg : (719859 / 8000000) ≤ -Real.log (200000 / 218831) ∧
    -Real.log (200000 / 218831) ≤ (11247797 / 125000000) := by
  have h := checkLog_sound (w := (18831 / 418831)) (n := 12)
    (lo := (719859 / 8000000)) (hi := (11247797 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218831 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218831 / 200000) = 1/(200000 / 218831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5196 : Bounds (719859 / 8000000) (11247797 / 125000000) (Real.log (218831 / 200000)) := by
  have h := reflection_log_5196_neg
  have he : Real.log (218831 / 200000) = -Real.log (200000 / 218831) := by
    rw [show ((218831 / 200000) : ℝ) = ((200000 / 218831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5197_neg : (98887069 / 1000000000) ≤ -Real.log (181169 / 200000) ∧
    -Real.log (181169 / 200000) ≤ (9888707 / 100000000) := by
  have h := checkLog_sound (w := (18831 / 381169)) (n := 12)
    (lo := (98887069 / 1000000000)) (hi := (9888707 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 181169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 181169) = 1/(181169 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5197 : Bounds (-9888707 / 100000000) (-98887069 / 1000000000) (Real.log (181169 / 200000)) := by
  have h := reflection_log_5197_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5198_neg : (90199871 / 1000000000) ≤ -Real.log (1000000 / 1094393) ∧
    -Real.log (1000000 / 1094393) ≤ (1409373 / 15625000) := by
  have h := checkLog_sound (w := (94393 / 2094393)) (n := 12)
    (lo := (90199871 / 1000000000)) (hi := (1409373 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094393 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094393 / 1000000) = 1/(1000000 / 1094393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5198 : Bounds (90199871 / 1000000000) (1409373 / 15625000) (Real.log (1094393 / 1000000)) := by
  have h := reflection_log_5198_neg
  have he : Real.log (1094393 / 1000000) = -Real.log (1000000 / 1094393) := by
    rw [show ((1094393 / 1000000) : ℝ) = ((1000000 / 1094393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5199_neg : (99149841 / 1000000000) ≤ -Real.log (905607 / 1000000) ∧
    -Real.log (905607 / 1000000) ≤ (49574921 / 500000000) := by
  have h := checkLog_sound (w := (94393 / 1905607)) (n := 12)
    (lo := (99149841 / 1000000000)) (hi := (49574921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905607) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905607) = 1/(905607 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5199 : Bounds (-49574921 / 500000000) (-99149841 / 1000000000) (Real.log (905607 / 1000000)) := by
  have h := reflection_log_5199_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5200_neg : (894997 / 100000000) ≤ -Real.log (991089961551 / 1000000000000) ∧
    -Real.log (991089961551 / 1000000000000) ≤ (8949971 / 1000000000) := by
  have h := checkLog_sound (w := (8910038449 / 1991089961551)) (n := 12)
    (lo := (894997 / 100000000)) (hi := (8949971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991089961551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991089961551) = 1/(991089961551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5200 : Bounds (-8949971 / 1000000000) (-894997 / 100000000) (Real.log (991089961551 / 1000000000000)) := by
  have h := reflection_log_5200_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5201_neg : (8904693 / 1000000000) ≤ -Real.log (39645393439 / 40000000000) ∧
    -Real.log (39645393439 / 40000000000) ≤ (4452347 / 500000000) := by
  have h := checkLog_sound (w := (354606561 / 79645393439)) (n := 12)
    (lo := (8904693 / 1000000000)) (hi := (4452347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39645393439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39645393439) = 1/(39645393439 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5201 : Bounds (-4452347 / 500000000) (-8904693 / 1000000000) (Real.log (39645393439 / 40000000000)) := by
  have h := reflection_log_5201_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5202_neg : (37773889 / 200000000) ≤ -Real.log (250000000000 / 301970811783) ∧
    -Real.log (250000000000 / 301970811783) ≤ (94434723 / 500000000) := by
  have h := checkLog_sound (w := (51970811783 / 551970811783)) (n := 12)
    (lo := (37773889 / 200000000)) (hi := (94434723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((301970811783 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(301970811783 / 250000000000) = 1/(250000000000 / 301970811783) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5202 : Bounds (37773889 / 200000000) (94434723 / 500000000) (Real.log (301970811783 / 250000000000)) := by
  have h := reflection_log_5202_neg
  have he : Real.log (301970811783 / 250000000000) = -Real.log (250000000000 / 301970811783) := by
    rw [show ((301970811783 / 250000000000) : ℝ) = ((250000000000 / 301970811783) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5203_neg : (189349713 / 1000000000) ≤ -Real.log (250000000000 / 302115873663) ∧
    -Real.log (250000000000 / 302115873663) ≤ (94674857 / 500000000) := by
  have h := checkLog_sound (w := (52115873663 / 552115873663)) (n := 12)
    (lo := (189349713 / 1000000000)) (hi := (94674857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302115873663 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302115873663 / 250000000000) = 1/(250000000000 / 302115873663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5203 : Bounds (189349713 / 1000000000) (94674857 / 500000000) (Real.log (302115873663 / 250000000000)) := by
  have h := reflection_log_5203_neg
  have he : Real.log (302115873663 / 250000000000) = -Real.log (250000000000 / 302115873663) := by
    rw [show ((302115873663 / 250000000000) : ℝ) = ((250000000000 / 302115873663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5204_neg : (189537531 / 500000000) ≤ -Real.log (100000000000 / 146093269349) ∧
    -Real.log (100000000000 / 146093269349) ≤ (379075063 / 1000000000) := by
  have h := checkLog_sound (w := (46093269349 / 246093269349)) (n := 12)
    (lo := (189537531 / 500000000)) (hi := (379075063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146093269349 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146093269349 / 100000000000) = 1/(100000000000 / 146093269349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5204 : Bounds (189537531 / 500000000) (379075063 / 1000000000) (Real.log (146093269349 / 100000000000)) := by
  have h := reflection_log_5204_neg
  have he : Real.log (146093269349 / 100000000000) = -Real.log (100000000000 / 146093269349) := by
    rw [show ((146093269349 / 100000000000) : ℝ) = ((100000000000 / 146093269349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5205_neg : (189641169 / 500000000) ≤ -Real.log (500000000000 / 730617770121) ∧
    -Real.log (500000000000 / 730617770121) ≤ (379282339 / 1000000000) := by
  have h := checkLog_sound (w := (230617770121 / 1230617770121)) (n := 12)
    (lo := (189641169 / 500000000)) (hi := (379282339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((730617770121 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(730617770121 / 500000000000) = 1/(500000000000 / 730617770121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5205 : Bounds (189641169 / 500000000) (379282339 / 1000000000) (Real.log (730617770121 / 500000000000)) := by
  have h := reflection_log_5205_neg
  have he : Real.log (730617770121 / 500000000000) = -Real.log (500000000000 / 730617770121) := by
    rw [show ((730617770121 / 500000000000) : ℝ) = ((500000000000 / 730617770121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5206_neg : (10740641 / 62500000) ≤ -Real.log (16 / 19) ∧
    -Real.log (16 / 19) ≤ (171850257 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 35)) (n := 12)
    (lo := (10740641 / 62500000)) (hi := (171850257 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19 / 16) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19 / 16) = 1/(16 / 19) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5206 : Bounds (10740641 / 62500000) (171850257 / 1000000000) (Real.log (19 / 16)) := by
  have h := reflection_log_5206_neg
  have he : Real.log (19 / 16) = -Real.log (16 / 19) := by
    rw [show ((19 / 16) : ℝ) = ((16 / 19) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5207_neg : (51909841 / 250000000) ≤ -Real.log (13 / 16) ∧
    -Real.log (13 / 16) ≤ (41527873 / 200000000) := by
  have h := checkLog_sound (w := (3 / 29)) (n := 12)
    (lo := (51909841 / 250000000)) (hi := (41527873 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 13) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16 / 13) = 1/(13 / 16) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5207 : Bounds (-41527873 / 200000000) (-51909841 / 250000000) (Real.log (13 / 16)) := by
  have h := reflection_log_5207_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5208_neg : (93741 / 500000000) ≤ -Real.log (16000 / 16003) ∧
    -Real.log (16000 / 16003) ≤ (187483 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 32003)) (n := 12)
    (lo := (93741 / 500000000)) (hi := (187483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16003 / 16000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16003 / 16000) = 1/(16000 / 16003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5208 : Bounds (93741 / 500000000) (187483 / 1000000000) (Real.log (16003 / 16000)) := by
  have h := reflection_log_5208_neg
  have he : Real.log (16003 / 16000) = -Real.log (16000 / 16003) := by
    rw [show ((16003 / 16000) : ℝ) = ((16000 / 16003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5209_neg : (187517 / 1000000000) ≤ -Real.log (15997 / 16000) ∧
    -Real.log (15997 / 16000) ≤ (93759 / 500000000) := by
  have h := checkLog_sound (w := (3 / 31997)) (n := 12)
    (lo := (187517 / 1000000000)) (hi := (93759 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16000 / 15997) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16000 / 15997) = 1/(15997 / 16000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5209 : Bounds (-93759 / 500000000) (-187517 / 1000000000) (Real.log (15997 / 16000)) := by
  have h := reflection_log_5209_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5210_neg : (45014493 / 500000000) ≤ -Real.log (500000 / 547103) ∧
    -Real.log (500000 / 547103) ≤ (90028987 / 1000000000) := by
  have h := checkLog_sound (w := (47103 / 1047103)) (n := 12)
    (lo := (45014493 / 500000000)) (hi := (90028987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547103 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547103 / 500000) = 1/(500000 / 547103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5210 : Bounds (45014493 / 500000000) (90028987 / 1000000000) (Real.log (547103 / 500000)) := by
  have h := reflection_log_5210_neg
  have he : Real.log (547103 / 500000) = -Real.log (500000 / 547103) := by
    rw [show ((547103 / 500000) : ℝ) = ((500000 / 547103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5211_neg : (98943371 / 1000000000) ≤ -Real.log (452897 / 500000) ∧
    -Real.log (452897 / 500000) ≤ (24735843 / 250000000) := by
  have h := checkLog_sound (w := (47103 / 952897)) (n := 12)
    (lo := (98943371 / 1000000000)) (hi := (24735843 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 452897) = 1/(452897 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5211 : Bounds (-24735843 / 250000000) (-98943371 / 1000000000) (Real.log (452897 / 500000)) := by
  have h := reflection_log_5211_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5212_neg : (90246471 / 1000000000) ≤ -Real.log (250000 / 273611) ∧
    -Real.log (250000 / 273611) ≤ (11280809 / 125000000) := by
  have h := checkLog_sound (w := (23611 / 523611)) (n := 12)
    (lo := (90246471 / 1000000000)) (hi := (11280809 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273611 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273611 / 250000) = 1/(250000 / 273611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5212 : Bounds (90246471 / 1000000000) (11280809 / 125000000) (Real.log (273611 / 250000)) := by
  have h := reflection_log_5212_neg
  have he : Real.log (273611 / 250000) = -Real.log (250000 / 273611) := by
    rw [show ((273611 / 250000) : ℝ) = ((250000 / 273611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5213_neg : (99206159 / 1000000000) ≤ -Real.log (226389 / 250000) ∧
    -Real.log (226389 / 250000) ≤ (1240077 / 12500000) := by
  have h := checkLog_sound (w := (23611 / 476389)) (n := 12)
    (lo := (99206159 / 1000000000)) (hi := (1240077 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226389) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226389) = 1/(226389 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5213 : Bounds (-1240077 / 12500000) (-99206159 / 1000000000) (Real.log (226389 / 250000)) := by
  have h := reflection_log_5213_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5214_neg : (8959687 / 1000000000) ≤ -Real.log (61942520679 / 62500000000) ∧
    -Real.log (61942520679 / 62500000000) ≤ (1119961 / 125000000) := by
  have h := checkLog_sound (w := (557479321 / 124442520679)) (n := 12)
    (lo := (8959687 / 1000000000)) (hi := (1119961 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61942520679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61942520679) = 1/(61942520679 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5214 : Bounds (-1119961 / 125000000) (-8959687 / 1000000000) (Real.log (61942520679 / 62500000000)) := by
  have h := reflection_log_5214_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5215_neg : (1782877 / 200000000) ≤ -Real.log (247781307391 / 250000000000) ∧
    -Real.log (247781307391 / 250000000000) ≤ (4457193 / 500000000) := by
  have h := checkLog_sound (w := (2218692609 / 497781307391)) (n := 12)
    (lo := (1782877 / 200000000)) (hi := (4457193 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247781307391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247781307391) = 1/(247781307391 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5215 : Bounds (-4457193 / 500000000) (-1782877 / 200000000) (Real.log (247781307391 / 250000000000)) := by
  have h := reflection_log_5215_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5216_neg : (188972357 / 1000000000) ≤ -Real.log (125000000000 / 151000945027) ∧
    -Real.log (125000000000 / 151000945027) ≤ (94486179 / 500000000) := by
  have h := checkLog_sound (w := (26000945027 / 276000945027)) (n := 12)
    (lo := (188972357 / 1000000000)) (hi := (94486179 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((151000945027 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(151000945027 / 125000000000) = 1/(125000000000 / 151000945027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5216 : Bounds (188972357 / 1000000000) (94486179 / 500000000) (Real.log (151000945027 / 125000000000)) := by
  have h := reflection_log_5216_neg
  have he : Real.log (151000945027 / 125000000000) = -Real.log (125000000000 / 151000945027) := by
    rw [show ((151000945027 / 125000000000) : ℝ) = ((125000000000 / 151000945027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5217_neg : (189452631 / 1000000000) ≤ -Real.log (500000000000 / 604293936543) ∧
    -Real.log (500000000000 / 604293936543) ≤ (23681579 / 125000000) := by
  have h := checkLog_sound (w := (104293936543 / 1104293936543)) (n := 12)
    (lo := (189452631 / 1000000000)) (hi := (23681579 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((604293936543 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(604293936543 / 500000000000) = 1/(500000000000 / 604293936543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5217 : Bounds (189452631 / 1000000000) (23681579 / 125000000) (Real.log (604293936543 / 500000000000)) := by
  have h := reflection_log_5217_neg
  have he : Real.log (604293936543 / 500000000000) = -Real.log (500000000000 / 604293936543) := by
    rw [show ((604293936543 / 500000000000) : ℝ) = ((500000000000 / 604293936543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5218_neg : (189641169 / 500000000) ≤ -Real.log (12500000000 / 18265444253) ∧
    -Real.log (12500000000 / 18265444253) ≤ (379282339 / 1000000000) := by
  have h := checkLog_sound (w := (5765444253 / 30765444253)) (n := 12)
    (lo := (189641169 / 500000000)) (hi := (379282339 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18265444253 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18265444253 / 12500000000) = 1/(12500000000 / 18265444253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5218 : Bounds (189641169 / 500000000) (379282339 / 1000000000) (Real.log (18265444253 / 12500000000)) := by
  have h := reflection_log_5218_neg
  have he : Real.log (18265444253 / 12500000000) = -Real.log (12500000000 / 18265444253) := by
    rw [show ((18265444253 / 12500000000) : ℝ) = ((12500000000 / 18265444253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5219_neg : (379489621 / 1000000000) ≤ -Real.log (50000000000 / 73076923077) ∧
    -Real.log (50000000000 / 73076923077) ≤ (189744811 / 500000000) := by
  have h := checkLog_sound (w := (23076923077 / 123076923077)) (n := 12)
    (lo := (379489621 / 1000000000)) (hi := (189744811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73076923077 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73076923077 / 50000000000) = 1/(50000000000 / 73076923077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5219 : Bounds (379489621 / 1000000000) (189744811 / 500000000) (Real.log (73076923077 / 50000000000)) := by
  have h := reflection_log_5219_neg
  have he : Real.log (73076923077 / 50000000000) = -Real.log (50000000000 / 73076923077) := by
    rw [show ((73076923077 / 50000000000) : ℝ) = ((50000000000 / 73076923077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5220_neg : (171934463 / 1000000000) ≤ -Real.log (2500 / 2969) ∧
    -Real.log (2500 / 2969) ≤ (671619 / 3906250) := by
  have h := checkLog_sound (w := (469 / 5469)) (n := 12)
    (lo := (171934463 / 1000000000)) (hi := (671619 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2969 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2969 / 2500) = 1/(2500 / 2969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5220 : Bounds (171934463 / 1000000000) (671619 / 3906250) (Real.log (2969 / 2500)) := by
  have h := reflection_log_5220_neg
  have he : Real.log (2969 / 2500) = -Real.log (2500 / 2969) := by
    rw [show ((2969 / 2500) : ℝ) = ((2500 / 2969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5221_neg : (207762449 / 1000000000) ≤ -Real.log (2031 / 2500) ∧
    -Real.log (2031 / 2500) ≤ (4155249 / 20000000) := by
  have h := checkLog_sound (w := (469 / 4531)) (n := 12)
    (lo := (207762449 / 1000000000)) (hi := (4155249 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2031) = 1/(2031 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5221 : Bounds (-4155249 / 20000000) (-207762449 / 1000000000) (Real.log (2031 / 2500)) := by
  have h := reflection_log_5221_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5222_neg : (93791 / 500000000) ≤ -Real.log (2500000 / 2500469) ∧
    -Real.log (2500000 / 2500469) ≤ (187583 / 1000000000) := by
  have h := checkLog_sound (w := (469 / 5000469)) (n := 12)
    (lo := (93791 / 500000000)) (hi := (187583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500469 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500469 / 2500000) = 1/(2500000 / 2500469) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5222 : Bounds (93791 / 500000000) (187583 / 1000000000) (Real.log (2500469 / 2500000)) := by
  have h := reflection_log_5222_neg
  have he : Real.log (2500469 / 2500000) = -Real.log (2500000 / 2500469) := by
    rw [show ((2500469 / 2500000) : ℝ) = ((2500000 / 2500469) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5223_neg : (187617 / 1000000000) ≤ -Real.log (2499531 / 2500000) ∧
    -Real.log (2499531 / 2500000) ≤ (93809 / 500000000) := by
  have h := checkLog_sound (w := (469 / 4999531)) (n := 12)
    (lo := (187617 / 1000000000)) (hi := (93809 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499531) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499531) = 1/(2499531 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5223 : Bounds (-93809 / 500000000) (-187617 / 1000000000) (Real.log (2499531 / 2500000)) := by
  have h := reflection_log_5223_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5224_neg : (45037797 / 500000000) ≤ -Real.log (1000000 / 1094257) ∧
    -Real.log (1000000 / 1094257) ≤ (18015119 / 200000000) := by
  have h := checkLog_sound (w := (94257 / 2094257)) (n := 12)
    (lo := (45037797 / 500000000)) (hi := (18015119 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1094257 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1094257 / 1000000) = 1/(1000000 / 1094257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5224 : Bounds (45037797 / 500000000) (18015119 / 200000000) (Real.log (1094257 / 1000000)) := by
  have h := reflection_log_5224_neg
  have he : Real.log (1094257 / 1000000) = -Real.log (1000000 / 1094257) := by
    rw [show ((1094257 / 1000000) : ℝ) = ((1000000 / 1094257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5225_neg : (98999677 / 1000000000) ≤ -Real.log (905743 / 1000000) ∧
    -Real.log (905743 / 1000000) ≤ (49499839 / 500000000) := by
  have h := checkLog_sound (w := (94257 / 1905743)) (n := 12)
    (lo := (98999677 / 1000000000)) (hi := (49499839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 905743) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 905743) = 1/(905743 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5225 : Bounds (-49499839 / 500000000) (-98999677 / 1000000000) (Real.log (905743 / 1000000)) := by
  have h := reflection_log_5225_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5226_neg : (90293069 / 1000000000) ≤ -Real.log (200000 / 218899) ∧
    -Real.log (200000 / 218899) ≤ (9029307 / 100000000) := by
  have h := checkLog_sound (w := (18899 / 418899)) (n := 12)
    (lo := (90293069 / 1000000000)) (hi := (9029307 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218899 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(218899 / 200000) = 1/(200000 / 218899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5226 : Bounds (90293069 / 1000000000) (9029307 / 100000000) (Real.log (218899 / 200000)) := by
  have h := reflection_log_5226_neg
  have he : Real.log (218899 / 200000) = -Real.log (200000 / 218899) := by
    rw [show ((218899 / 200000) : ℝ) = ((200000 / 218899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5227_neg : (99262479 / 1000000000) ≤ -Real.log (181101 / 200000) ∧
    -Real.log (181101 / 200000) ≤ (1240781 / 12500000) := by
  have h := checkLog_sound (w := (18899 / 381101)) (n := 12)
    (lo := (99262479 / 1000000000)) (hi := (1240781 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 181101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 181101) = 1/(181101 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5227 : Bounds (-1240781 / 12500000) (-99262479 / 1000000000) (Real.log (181101 / 200000)) := by
  have h := reflection_log_5227_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5228_neg : (896941 / 100000000) ≤ -Real.log (39642827799 / 40000000000) ∧
    -Real.log (39642827799 / 40000000000) ≤ (8969411 / 1000000000) := by
  have h := checkLog_sound (w := (357172201 / 79642827799)) (n := 12)
    (lo := (896941 / 100000000)) (hi := (8969411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39642827799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39642827799) = 1/(39642827799 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5228 : Bounds (-8969411 / 1000000000) (-896941 / 100000000) (Real.log (39642827799 / 40000000000)) := by
  have h := reflection_log_5228_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5229_neg : (8924083 / 1000000000) ≤ -Real.log (991115617951 / 1000000000000) ∧
    -Real.log (991115617951 / 1000000000000) ≤ (2231021 / 250000000) := by
  have h := checkLog_sound (w := (8884382049 / 1991115617951)) (n := 12)
    (lo := (8924083 / 1000000000)) (hi := (2231021 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991115617951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991115617951) = 1/(991115617951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5229 : Bounds (-2231021 / 250000000) (-8924083 / 1000000000) (Real.log (991115617951 / 1000000000000)) := by
  have h := reflection_log_5229_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5230_neg : (189075271 / 1000000000) ≤ -Real.log (10000000000 / 12081318873) ∧
    -Real.log (10000000000 / 12081318873) ≤ (23634409 / 125000000) := by
  have h := checkLog_sound (w := (2081318873 / 22081318873)) (n := 12)
    (lo := (189075271 / 1000000000)) (hi := (23634409 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((12081318873 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(12081318873 / 10000000000) = 1/(10000000000 / 12081318873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5230 : Bounds (189075271 / 1000000000) (23634409 / 125000000) (Real.log (12081318873 / 10000000000)) := by
  have h := reflection_log_5230_neg
  have he : Real.log (12081318873 / 10000000000) = -Real.log (10000000000 / 12081318873) := by
    rw [show ((12081318873 / 10000000000) : ℝ) = ((10000000000 / 12081318873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5231_neg : (189555549 / 1000000000) ≤ -Real.log (250000000000 / 302178066383) ∧
    -Real.log (250000000000 / 302178066383) ≤ (3791111 / 20000000) := by
  have h := checkLog_sound (w := (52178066383 / 552178066383)) (n := 12)
    (lo := (189555549 / 1000000000)) (hi := (3791111 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302178066383 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302178066383 / 250000000000) = 1/(250000000000 / 302178066383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5231 : Bounds (189555549 / 1000000000) (3791111 / 20000000) (Real.log (302178066383 / 250000000000)) := by
  have h := reflection_log_5231_neg
  have he : Real.log (302178066383 / 250000000000) = -Real.log (250000000000 / 302178066383) := by
    rw [show ((302178066383 / 250000000000) : ℝ) = ((250000000000 / 302178066383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5232_neg : (379489621 / 1000000000) ≤ -Real.log (500000000000 / 730769230769) ∧
    -Real.log (500000000000 / 730769230769) ≤ (189744811 / 500000000) := by
  have h := checkLog_sound (w := (230769230769 / 1230769230769)) (n := 12)
    (lo := (379489621 / 1000000000)) (hi := (189744811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((730769230769 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(730769230769 / 500000000000) = 1/(500000000000 / 730769230769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5232 : Bounds (379489621 / 1000000000) (189744811 / 500000000) (Real.log (730769230769 / 500000000000)) := by
  have h := reflection_log_5232_neg
  have he : Real.log (730769230769 / 500000000000) = -Real.log (500000000000 / 730769230769) := by
    rw [show ((730769230769 / 500000000000) : ℝ) = ((500000000000 / 730769230769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5233_neg : (379696913 / 1000000000) ≤ -Real.log (250000000000 / 365460364353) ∧
    -Real.log (250000000000 / 365460364353) ≤ (189848457 / 500000000) := by
  have h := checkLog_sound (w := (115460364353 / 615460364353)) (n := 12)
    (lo := (379696913 / 1000000000)) (hi := (189848457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((365460364353 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(365460364353 / 250000000000) = 1/(250000000000 / 365460364353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5233 : Bounds (379696913 / 1000000000) (189848457 / 500000000) (Real.log (365460364353 / 250000000000)) := by
  have h := reflection_log_5233_neg
  have he : Real.log (365460364353 / 250000000000) = -Real.log (250000000000 / 365460364353) := by
    rw [show ((365460364353 / 250000000000) : ℝ) = ((250000000000 / 365460364353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5234_neg : (172018663 / 1000000000) ≤ -Real.log (10000 / 11877) ∧
    -Real.log (10000 / 11877) ≤ (21502333 / 125000000) := by
  have h := checkLog_sound (w := (1877 / 21877)) (n := 12)
    (lo := (172018663 / 1000000000)) (hi := (21502333 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11877 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11877 / 10000) = 1/(10000 / 11877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5234 : Bounds (172018663 / 1000000000) (21502333 / 125000000) (Real.log (11877 / 10000)) := by
  have h := reflection_log_5234_neg
  have he : Real.log (11877 / 10000) = -Real.log (10000 / 11877) := by
    rw [show ((11877 / 10000) : ℝ) = ((10000 / 11877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5235_neg : (51971387 / 250000000) ≤ -Real.log (8123 / 10000) ∧
    -Real.log (8123 / 10000) ≤ (207885549 / 1000000000) := by
  have h := checkLog_sound (w := (1877 / 18123)) (n := 12)
    (lo := (51971387 / 250000000)) (hi := (207885549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8123) = 1/(8123 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5235 : Bounds (-207885549 / 1000000000) (-51971387 / 250000000) (Real.log (8123 / 10000)) := by
  have h := reflection_log_5235_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5236_neg : (93841 / 500000000) ≤ -Real.log (10000000 / 10001877) ∧
    -Real.log (10000000 / 10001877) ≤ (187683 / 1000000000) := by
  have h := checkLog_sound (w := (1877 / 20001877)) (n := 12)
    (lo := (93841 / 500000000)) (hi := (187683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001877 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001877 / 10000000) = 1/(10000000 / 10001877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5236 : Bounds (93841 / 500000000) (187683 / 1000000000) (Real.log (10001877 / 10000000)) := by
  have h := reflection_log_5236_neg
  have he : Real.log (10001877 / 10000000) = -Real.log (10000000 / 10001877) := by
    rw [show ((10001877 / 10000000) : ℝ) = ((10000000 / 10001877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5237_neg : (187717 / 1000000000) ≤ -Real.log (9998123 / 10000000) ∧
    -Real.log (9998123 / 10000000) ≤ (93859 / 500000000) := by
  have h := checkLog_sound (w := (1877 / 19998123)) (n := 12)
    (lo := (187717 / 1000000000)) (hi := (93859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998123) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998123) = 1/(9998123 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5237 : Bounds (-93859 / 500000000) (-187717 / 1000000000) (Real.log (9998123 / 10000000)) := by
  have h := reflection_log_5237_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5238_neg : (450611 / 5000000) ≤ -Real.log (250000 / 273577) ∧
    -Real.log (250000 / 273577) ≤ (90122201 / 1000000000) := by
  have h := checkLog_sound (w := (23577 / 523577)) (n := 12)
    (lo := (450611 / 5000000)) (hi := (90122201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273577 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273577 / 250000) = 1/(250000 / 273577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5238 : Bounds (450611 / 5000000) (90122201 / 1000000000) (Real.log (273577 / 250000)) := by
  have h := reflection_log_5238_neg
  have he : Real.log (273577 / 250000) = -Real.log (250000 / 273577) := by
    rw [show ((273577 / 250000) : ℝ) = ((250000 / 273577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5239_neg : (49527993 / 500000000) ≤ -Real.log (226423 / 250000) ∧
    -Real.log (226423 / 250000) ≤ (99055987 / 1000000000) := by
  have h := checkLog_sound (w := (23577 / 476423)) (n := 12)
    (lo := (49527993 / 500000000)) (hi := (99055987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 226423) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 226423) = 1/(226423 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5239 : Bounds (-99055987 / 1000000000) (-49527993 / 500000000) (Real.log (226423 / 250000)) := by
  have h := reflection_log_5239_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5240_neg : (18067933 / 200000000) ≤ -Real.log (500000 / 547273) ∧
    -Real.log (500000 / 547273) ≤ (45169833 / 500000000) := by
  have h := checkLog_sound (w := (47273 / 1047273)) (n := 12)
    (lo := (18067933 / 200000000)) (hi := (45169833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((547273 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(547273 / 500000) = 1/(500000 / 547273) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5240 : Bounds (18067933 / 200000000) (45169833 / 500000000) (Real.log (547273 / 500000)) := by
  have h := reflection_log_5240_neg
  have he : Real.log (547273 / 500000) = -Real.log (500000 / 547273) := by
    rw [show ((547273 / 500000) : ℝ) = ((500000 / 547273) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5241_neg : (99318803 / 1000000000) ≤ -Real.log (452727 / 500000) ∧
    -Real.log (452727 / 500000) ≤ (24829701 / 250000000) := by
  have h := checkLog_sound (w := (47273 / 952727)) (n := 12)
    (lo := (99318803 / 1000000000)) (hi := (24829701 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 452727) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 452727) = 1/(452727 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5241 : Bounds (-24829701 / 250000000) (-99318803 / 1000000000) (Real.log (452727 / 500000)) := by
  have h := reflection_log_5241_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5242_neg : (4489569 / 500000000) ≤ -Real.log (247765263471 / 250000000000) ∧
    -Real.log (247765263471 / 250000000000) ≤ (8979139 / 1000000000) := by
  have h := checkLog_sound (w := (2234736529 / 497765263471)) (n := 12)
    (lo := (4489569 / 500000000)) (hi := (8979139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247765263471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247765263471) = 1/(247765263471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5242 : Bounds (-8979139 / 1000000000) (-4489569 / 500000000) (Real.log (247765263471 / 250000000000)) := by
  have h := reflection_log_5242_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5243_neg : (4466893 / 500000000) ≤ -Real.log (61944125071 / 62500000000) ∧
    -Real.log (61944125071 / 62500000000) ≤ (8933787 / 1000000000) := by
  have h := checkLog_sound (w := (555874929 / 124444125071)) (n := 12)
    (lo := (4466893 / 500000000)) (hi := (8933787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61944125071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61944125071) = 1/(61944125071 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5243 : Bounds (-8933787 / 1000000000) (-4466893 / 500000000) (Real.log (61944125071 / 62500000000)) := by
  have h := reflection_log_5243_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5244_neg : (94589093 / 500000000) ≤ -Real.log (500000000000 / 604128114193) ∧
    -Real.log (500000000000 / 604128114193) ≤ (189178187 / 1000000000) := by
  have h := checkLog_sound (w := (104128114193 / 1104128114193)) (n := 12)
    (lo := (94589093 / 500000000)) (hi := (189178187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((604128114193 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(604128114193 / 500000000000) = 1/(500000000000 / 604128114193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5244 : Bounds (94589093 / 500000000) (189178187 / 1000000000) (Real.log (604128114193 / 500000000000)) := by
  have h := reflection_log_5244_neg
  have he : Real.log (604128114193 / 500000000000) = -Real.log (500000000000 / 604128114193) := by
    rw [show ((604128114193 / 500000000000) : ℝ) = ((500000000000 / 604128114193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5245_neg : (189658469 / 1000000000) ≤ -Real.log (100000000000 / 120883667199) ∧
    -Real.log (100000000000 / 120883667199) ≤ (18965847 / 100000000) := by
  have h := checkLog_sound (w := (20883667199 / 220883667199)) (n := 12)
    (lo := (189658469 / 1000000000)) (hi := (18965847 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((120883667199 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(120883667199 / 100000000000) = 1/(100000000000 / 120883667199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5245 : Bounds (189658469 / 1000000000) (18965847 / 100000000) (Real.log (120883667199 / 100000000000)) := by
  have h := reflection_log_5245_neg
  have he : Real.log (120883667199 / 100000000000) = -Real.log (100000000000 / 120883667199) := by
    rw [show ((120883667199 / 100000000000) : ℝ) = ((100000000000 / 120883667199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5246_neg : (379696913 / 1000000000) ≤ -Real.log (100000000000 / 146184145741) ∧
    -Real.log (100000000000 / 146184145741) ≤ (189848457 / 500000000) := by
  have h := checkLog_sound (w := (46184145741 / 246184145741)) (n := 12)
    (lo := (379696913 / 1000000000)) (hi := (189848457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146184145741 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146184145741 / 100000000000) = 1/(100000000000 / 146184145741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5246 : Bounds (379696913 / 1000000000) (189848457 / 500000000) (Real.log (146184145741 / 100000000000)) := by
  have h := reflection_log_5246_neg
  have he : Real.log (146184145741 / 100000000000) = -Real.log (100000000000 / 146184145741) := by
    rw [show ((146184145741 / 100000000000) : ℝ) = ((100000000000 / 146184145741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_5247_neg : (94976053 / 250000000) ≤ -Real.log (250000000000 / 365536131971) ∧
    -Real.log (250000000000 / 365536131971) ≤ (379904213 / 1000000000) := by
  have h := checkLog_sound (w := (115536131971 / 615536131971)) (n := 12)
    (lo := (94976053 / 250000000)) (hi := (379904213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((365536131971 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(365536131971 / 250000000000) = 1/(250000000000 / 365536131971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5247 : Bounds (94976053 / 250000000) (379904213 / 1000000000) (Real.log (365536131971 / 250000000000)) := by
  have h := reflection_log_5247_neg
  have he : Real.log (365536131971 / 250000000000) = -Real.log (250000000000 / 365536131971) := by
    rw [show ((365536131971 / 250000000000) : ℝ) = ((250000000000 / 365536131971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
