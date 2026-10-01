import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1280_neg : (83542491 / 1000000000) ≤ -Real.log (229963 / 250000) ∧
    -Real.log (229963 / 250000) ≤ (20885623 / 250000000) := by
  have h := checkLog_sound (w := (20037 / 479963)) (n := 12)
    (lo := (83542491 / 1000000000)) (hi := (20885623 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229963) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229963) = 1/(229963 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1280 : Bounds (-20885623 / 250000000) (-83542491 / 1000000000) (Real.log (229963 / 250000)) := by
  have h := reflection_log_1280_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1281_neg : (3222211 / 500000000) ≤ -Real.log (62098518631 / 62500000000) ∧
    -Real.log (62098518631 / 62500000000) ≤ (6444423 / 1000000000) := by
  have h := checkLog_sound (w := (401481369 / 124598518631)) (n := 12)
    (lo := (3222211 / 500000000)) (hi := (6444423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62098518631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62098518631) = 1/(62098518631 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1281 : Bounds (-6444423 / 1000000000) (-3222211 / 500000000) (Real.log (62098518631 / 62500000000)) := by
  have h := reflection_log_1281_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1282_neg : (3205213 / 500000000) ≤ -Real.log (993610076031 / 1000000000000) ∧
    -Real.log (993610076031 / 1000000000000) ≤ (6410427 / 1000000000) := by
  have h := checkLog_sound (w := (6389923969 / 1993610076031)) (n := 12)
    (lo := (3205213 / 500000000)) (hi := (6410427 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993610076031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993610076031) = 1/(993610076031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1282 : Bounds (-6410427 / 1000000000) (-3205213 / 500000000) (Real.log (993610076031 / 1000000000000)) := by
  have h := reflection_log_1282_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1283_neg : (160215839 / 1000000000) ≤ -Real.log (500000000000 / 586882093943) ∧
    -Real.log (500000000000 / 586882093943) ≤ (1001349 / 6250000) := by
  have h := checkLog_sound (w := (86882093943 / 1086882093943)) (n := 12)
    (lo := (160215839 / 1000000000)) (hi := (1001349 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586882093943 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586882093943 / 500000000000) = 1/(500000000000 / 586882093943) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1283 : Bounds (160215839 / 1000000000) (1001349 / 6250000) (Real.log (586882093943 / 500000000000)) := by
  have h := reflection_log_1283_neg
  have he : Real.log (586882093943 / 500000000000) = -Real.log (500000000000 / 586882093943) := by
    rw [show ((586882093943 / 500000000000) : ℝ) = ((500000000000 / 586882093943) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1284_neg : (2008007 / 12500000) ≤ -Real.log (500000000000 / 587131408097) ∧
    -Real.log (500000000000 / 587131408097) ≤ (160640561 / 1000000000) := by
  have h := checkLog_sound (w := (87131408097 / 1087131408097)) (n := 12)
    (lo := (2008007 / 12500000)) (hi := (160640561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587131408097 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587131408097 / 500000000000) = 1/(500000000000 / 587131408097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1284 : Bounds (2008007 / 12500000) (160640561 / 1000000000) (Real.log (587131408097 / 500000000000)) := by
  have h := reflection_log_1284_neg
  have he : Real.log (587131408097 / 500000000000) = -Real.log (500000000000 / 587131408097) := by
    rw [show ((587131408097 / 500000000000) : ℝ) = ((500000000000 / 587131408097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1285_neg : (12853471 / 40000000) ≤ -Real.log (100000000000 / 137896990603) ∧
    -Real.log (100000000000 / 137896990603) ≤ (40167097 / 125000000) := by
  have h := checkLog_sound (w := (37896990603 / 237896990603)) (n := 12)
    (lo := (12853471 / 40000000)) (hi := (40167097 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((137896990603 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(137896990603 / 100000000000) = 1/(100000000000 / 137896990603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1285 : Bounds (12853471 / 40000000) (40167097 / 125000000) (Real.log (137896990603 / 100000000000)) := by
  have h := reflection_log_1285_neg
  have he : Real.log (137896990603 / 100000000000) = -Real.log (100000000000 / 137896990603) := by
    rw [show ((137896990603 / 100000000000) : ℝ) = ((100000000000 / 137896990603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1286_neg : (160770993 / 500000000) ≤ -Real.log (500000000000 / 689626457293) ∧
    -Real.log (500000000000 / 689626457293) ≤ (321541987 / 1000000000) := by
  have h := checkLog_sound (w := (189626457293 / 1189626457293)) (n := 12)
    (lo := (160770993 / 500000000)) (hi := (321541987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((689626457293 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(689626457293 / 500000000000) = 1/(500000000000 / 689626457293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1286 : Bounds (160770993 / 500000000) (321541987 / 1000000000) (Real.log (689626457293 / 500000000000)) := by
  have h := reflection_log_1286_neg
  have he : Real.log (689626457293 / 500000000000) = -Real.log (500000000000 / 689626457293) := by
    rw [show ((689626457293 / 500000000000) : ℝ) = ((500000000000 / 689626457293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1287_neg : (147988877 / 1000000000) ≤ -Real.log (2000 / 2319) ∧
    -Real.log (2000 / 2319) ≤ (73994439 / 500000000) := by
  have h := checkLog_sound (w := (319 / 4319)) (n := 12)
    (lo := (147988877 / 1000000000)) (hi := (73994439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2319 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2319 / 2000) = 1/(2000 / 2319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1287 : Bounds (147988877 / 1000000000) (73994439 / 500000000) (Real.log (2319 / 2000)) := by
  have h := reflection_log_1287_neg
  have he : Real.log (2319 / 2000) = -Real.log (2000 / 2319) := by
    rw [show ((2319 / 2000) : ℝ) = ((2000 / 2319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1288_neg : (86879163 / 500000000) ≤ -Real.log (1681 / 2000) ∧
    -Real.log (1681 / 2000) ≤ (173758327 / 1000000000) := by
  have h := checkLog_sound (w := (319 / 3681)) (n := 12)
    (lo := (86879163 / 500000000)) (hi := (173758327 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1681) = 1/(1681 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1288 : Bounds (-173758327 / 1000000000) (-86879163 / 500000000) (Real.log (1681 / 2000)) := by
  have h := reflection_log_1288_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1289_neg : (159487 / 1000000000) ≤ -Real.log (2000000 / 2000319) ∧
    -Real.log (2000000 / 2000319) ≤ (623 / 3906250) := by
  have h := checkLog_sound (w := (319 / 4000319)) (n := 12)
    (lo := (159487 / 1000000000)) (hi := (623 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000319 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000319 / 2000000) = 1/(2000000 / 2000319) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1289 : Bounds (159487 / 1000000000) (623 / 3906250) (Real.log (2000319 / 2000000)) := by
  have h := reflection_log_1289_neg
  have he : Real.log (2000319 / 2000000) = -Real.log (2000000 / 2000319) := by
    rw [show ((2000319 / 2000000) : ℝ) = ((2000000 / 2000319) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1290_neg : (19939 / 125000000) ≤ -Real.log (1999681 / 2000000) ∧
    -Real.log (1999681 / 2000000) ≤ (159513 / 1000000000) := by
  have h := checkLog_sound (w := (319 / 3999681)) (n := 12)
    (lo := (19939 / 125000000)) (hi := (159513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999681) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999681) = 1/(1999681 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1290 : Bounds (-159513 / 1000000000) (-19939 / 125000000) (Real.log (1999681 / 2000000)) := by
  have h := reflection_log_1290_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1291_neg : (76949929 / 1000000000) ≤ -Real.log (250000 / 269997) ∧
    -Real.log (250000 / 269997) ≤ (7694993 / 100000000) := by
  have h := checkLog_sound (w := (19997 / 519997)) (n := 12)
    (lo := (76949929 / 1000000000)) (hi := (7694993 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269997 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269997 / 250000) = 1/(250000 / 269997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1291 : Bounds (76949929 / 1000000000) (7694993 / 100000000) (Real.log (269997 / 250000)) := by
  have h := reflection_log_1291_neg
  have he : Real.log (269997 / 250000) = -Real.log (250000 / 269997) := by
    rw [show ((269997 / 250000) : ℝ) = ((250000 / 269997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1292_neg : (16673713 / 200000000) ≤ -Real.log (230003 / 250000) ∧
    -Real.log (230003 / 250000) ≤ (41684283 / 500000000) := by
  have h := checkLog_sound (w := (19997 / 480003)) (n := 12)
    (lo := (16673713 / 200000000)) (hi := (41684283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230003) = 1/(230003 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1292 : Bounds (-41684283 / 500000000) (-16673713 / 200000000) (Real.log (230003 / 250000)) := by
  have h := reflection_log_1292_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1293_neg : (77145283 / 1000000000) ≤ -Real.log (1000000 / 1080199) ∧
    -Real.log (1000000 / 1080199) ≤ (19286321 / 250000000) := by
  have h := checkLog_sound (w := (80199 / 2080199)) (n := 12)
    (lo := (77145283 / 1000000000)) (hi := (19286321 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080199 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080199 / 1000000) = 1/(1000000 / 1080199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1293 : Bounds (77145283 / 1000000000) (19286321 / 250000000) (Real.log (1080199 / 1000000)) := by
  have h := reflection_log_1293_neg
  have he : Real.log (1080199 / 1000000) = -Real.log (1000000 / 1080199) := by
    rw [show ((1080199 / 1000000) : ℝ) = ((1000000 / 1080199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1294_neg : (5224871 / 62500000) ≤ -Real.log (919801 / 1000000) ∧
    -Real.log (919801 / 1000000) ≤ (83597937 / 1000000000) := by
  have h := checkLog_sound (w := (80199 / 1919801)) (n := 12)
    (lo := (5224871 / 62500000)) (hi := (83597937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919801) = 1/(919801 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1294 : Bounds (-83597937 / 1000000000) (-5224871 / 62500000) (Real.log (919801 / 1000000)) := by
  have h := reflection_log_1294_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1295_neg : (6452653 / 1000000000) ≤ -Real.log (993568120399 / 1000000000000) ∧
    -Real.log (993568120399 / 1000000000000) ≤ (3226327 / 500000000) := by
  have h := checkLog_sound (w := (6431879601 / 1993568120399)) (n := 12)
    (lo := (6452653 / 1000000000)) (hi := (3226327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993568120399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993568120399) = 1/(993568120399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1295 : Bounds (-3226327 / 500000000) (-6452653 / 1000000000) (Real.log (993568120399 / 1000000000000)) := by
  have h := reflection_log_1295_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1296_neg : (1283727 / 200000000) ≤ -Real.log (62100119991 / 62500000000) ∧
    -Real.log (62100119991 / 62500000000) ≤ (1604659 / 250000000) := by
  have h := checkLog_sound (w := (399880009 / 124600119991)) (n := 12)
    (lo := (1283727 / 200000000)) (hi := (1604659 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62100119991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62100119991) = 1/(62100119991 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1296 : Bounds (-1604659 / 250000000) (-1283727 / 200000000) (Real.log (62100119991 / 62500000000)) := by
  have h := reflection_log_1296_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1297_neg : (32063699 / 200000000) ≤ -Real.log (50000000000 / 58694234423) ∧
    -Real.log (50000000000 / 58694234423) ≤ (5009953 / 31250000) := by
  have h := checkLog_sound (w := (8694234423 / 108694234423)) (n := 12)
    (lo := (32063699 / 200000000)) (hi := (5009953 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58694234423 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58694234423 / 50000000000) = 1/(50000000000 / 58694234423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1297 : Bounds (32063699 / 200000000) (5009953 / 31250000) (Real.log (58694234423 / 50000000000)) := by
  have h := reflection_log_1297_neg
  have he : Real.log (58694234423 / 50000000000) = -Real.log (50000000000 / 58694234423) := by
    rw [show ((58694234423 / 50000000000) : ℝ) = ((50000000000 / 58694234423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1298_neg : (8037161 / 50000000) ≤ -Real.log (125000000000 / 146797921507) ∧
    -Real.log (125000000000 / 146797921507) ≤ (160743221 / 1000000000) := by
  have h := checkLog_sound (w := (21797921507 / 271797921507)) (n := 12)
    (lo := (8037161 / 50000000)) (hi := (160743221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146797921507 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146797921507 / 125000000000) = 1/(125000000000 / 146797921507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1298 : Bounds (8037161 / 50000000) (160743221 / 1000000000) (Real.log (146797921507 / 125000000000)) := by
  have h := reflection_log_1298_neg
  have he : Real.log (146797921507 / 125000000000) = -Real.log (125000000000 / 146797921507) := by
    rw [show ((146797921507 / 125000000000) : ℝ) = ((125000000000 / 146797921507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1299_neg : (160770993 / 500000000) ≤ -Real.log (125000000000 / 172406614323) ∧
    -Real.log (125000000000 / 172406614323) ≤ (321541987 / 1000000000) := by
  have h := checkLog_sound (w := (47406614323 / 297406614323)) (n := 12)
    (lo := (160770993 / 500000000)) (hi := (321541987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172406614323 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172406614323 / 125000000000) = 1/(125000000000 / 172406614323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1299 : Bounds (160770993 / 500000000) (321541987 / 1000000000) (Real.log (172406614323 / 125000000000)) := by
  have h := reflection_log_1299_neg
  have he : Real.log (172406614323 / 125000000000) = -Real.log (125000000000 / 172406614323) := by
    rw [show ((172406614323 / 125000000000) : ℝ) = ((125000000000 / 172406614323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1300_neg : (321747203 / 1000000000) ≤ -Real.log (500000000000 / 689767995241) ∧
    -Real.log (500000000000 / 689767995241) ≤ (80436801 / 250000000) := by
  have h := checkLog_sound (w := (189767995241 / 1189767995241)) (n := 12)
    (lo := (321747203 / 1000000000)) (hi := (80436801 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((689767995241 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(689767995241 / 500000000000) = 1/(500000000000 / 689767995241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1300 : Bounds (321747203 / 1000000000) (80436801 / 250000000) (Real.log (689767995241 / 500000000000)) := by
  have h := reflection_log_1300_neg
  have he : Real.log (689767995241 / 500000000000) = -Real.log (500000000000 / 689767995241) := by
    rw [show ((689767995241 / 500000000000) : ℝ) = ((500000000000 / 689767995241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1301_neg : (74037559 / 500000000) ≤ -Real.log (2500 / 2899) ∧
    -Real.log (2500 / 2899) ≤ (148075119 / 1000000000) := by
  have h := checkLog_sound (w := (399 / 5399)) (n := 12)
    (lo := (74037559 / 500000000)) (hi := (148075119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2899 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2899 / 2500) = 1/(2500 / 2899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1301 : Bounds (74037559 / 500000000) (148075119 / 1000000000) (Real.log (2899 / 2500)) := by
  have h := reflection_log_1301_neg
  have he : Real.log (2899 / 2500) = -Real.log (2500 / 2899) := by
    rw [show ((2899 / 2500) : ℝ) = ((2500 / 2899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1302_neg : (17387731 / 100000000) ≤ -Real.log (2101 / 2500) ∧
    -Real.log (2101 / 2500) ≤ (173877311 / 1000000000) := by
  have h := checkLog_sound (w := (399 / 4601)) (n := 12)
    (lo := (17387731 / 100000000)) (hi := (173877311 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2101) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2101) = 1/(2101 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1302 : Bounds (-173877311 / 1000000000) (-17387731 / 100000000) (Real.log (2101 / 2500)) := by
  have h := reflection_log_1302_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1303_neg : (159587 / 1000000000) ≤ -Real.log (2500000 / 2500399) ∧
    -Real.log (2500000 / 2500399) ≤ (39897 / 250000000) := by
  have h := checkLog_sound (w := (399 / 5000399)) (n := 12)
    (lo := (159587 / 1000000000)) (hi := (39897 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500399 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500399 / 2500000) = 1/(2500000 / 2500399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1303 : Bounds (159587 / 1000000000) (39897 / 250000000) (Real.log (2500399 / 2500000)) := by
  have h := reflection_log_1303_neg
  have he : Real.log (2500399 / 2500000) = -Real.log (2500000 / 2500399) := by
    rw [show ((2500399 / 2500000) : ℝ) = ((2500000 / 2500399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1304_neg : (39903 / 250000000) ≤ -Real.log (2499601 / 2500000) ∧
    -Real.log (2499601 / 2500000) ≤ (159613 / 1000000000) := by
  have h := checkLog_sound (w := (399 / 4999601)) (n := 12)
    (lo := (39903 / 250000000)) (hi := (159613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499601) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499601) = 1/(2499601 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1304 : Bounds (-159613 / 1000000000) (-39903 / 250000000) (Real.log (2499601 / 2500000)) := by
  have h := reflection_log_1304_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1305_neg : (76997151 / 1000000000) ≤ -Real.log (1000000 / 1080039) ∧
    -Real.log (1000000 / 1080039) ≤ (2406161 / 31250000) := by
  have h := checkLog_sound (w := (80039 / 2080039)) (n := 12)
    (lo := (76997151 / 1000000000)) (hi := (2406161 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080039 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080039 / 1000000) = 1/(1000000 / 1080039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1305 : Bounds (76997151 / 1000000000) (2406161 / 31250000) (Real.log (1080039 / 1000000)) := by
  have h := reflection_log_1305_neg
  have he : Real.log (1080039 / 1000000) = -Real.log (1000000 / 1080039) := by
    rw [show ((1080039 / 1000000) : ℝ) = ((1000000 / 1080039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1306_neg : (83424001 / 1000000000) ≤ -Real.log (919961 / 1000000) ∧
    -Real.log (919961 / 1000000) ≤ (41712001 / 500000000) := by
  have h := checkLog_sound (w := (80039 / 1919961)) (n := 12)
    (lo := (83424001 / 1000000000)) (hi := (41712001 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919961) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919961) = 1/(919961 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1306 : Bounds (-41712001 / 500000000) (-83424001 / 1000000000) (Real.log (919961 / 1000000)) := by
  have h := reflection_log_1306_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1307_neg : (7719157 / 100000000) ≤ -Real.log (1000000 / 1080249) ∧
    -Real.log (1000000 / 1080249) ≤ (77191571 / 1000000000) := by
  have h := checkLog_sound (w := (80249 / 2080249)) (n := 12)
    (lo := (7719157 / 100000000)) (hi := (77191571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080249 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080249 / 1000000) = 1/(1000000 / 1080249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1307 : Bounds (7719157 / 100000000) (77191571 / 1000000000) (Real.log (1080249 / 1000000)) := by
  have h := reflection_log_1307_neg
  have he : Real.log (1080249 / 1000000) = -Real.log (1000000 / 1080249) := by
    rw [show ((1080249 / 1000000) : ℝ) = ((1000000 / 1080249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1308_neg : (83652297 / 1000000000) ≤ -Real.log (919751 / 1000000) ∧
    -Real.log (919751 / 1000000) ≤ (41826149 / 500000000) := by
  have h := checkLog_sound (w := (80249 / 1919751)) (n := 12)
    (lo := (83652297 / 1000000000)) (hi := (41826149 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919751) = 1/(919751 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1308 : Bounds (-41826149 / 500000000) (-83652297 / 1000000000) (Real.log (919751 / 1000000)) := by
  have h := reflection_log_1308_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1309_neg : (6460727 / 1000000000) ≤ -Real.log (993560097999 / 1000000000000) ∧
    -Real.log (993560097999 / 1000000000000) ≤ (807591 / 125000000) := by
  have h := checkLog_sound (w := (6439902001 / 1993560097999)) (n := 12)
    (lo := (6460727 / 1000000000)) (hi := (807591 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993560097999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993560097999) = 1/(993560097999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1309 : Bounds (-807591 / 125000000) (-6460727 / 1000000000) (Real.log (993560097999 / 1000000000000)) := by
  have h := reflection_log_1309_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1310_neg : (6426849 / 1000000000) ≤ -Real.log (993593758479 / 1000000000000) ∧
    -Real.log (993593758479 / 1000000000000) ≤ (128537 / 20000000) := by
  have h := checkLog_sound (w := (6406241521 / 1993593758479)) (n := 12)
    (lo := (6426849 / 1000000000)) (hi := (128537 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993593758479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993593758479) = 1/(993593758479 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1310 : Bounds (-128537 / 20000000) (-6426849 / 1000000000) (Real.log (993593758479 / 1000000000000)) := by
  have h := reflection_log_1310_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1311_neg : (5013161 / 31250000) ≤ -Real.log (500000000000 / 587002601197) ∧
    -Real.log (500000000000 / 587002601197) ≤ (160421153 / 1000000000) := by
  have h := checkLog_sound (w := (87002601197 / 1087002601197)) (n := 12)
    (lo := (5013161 / 31250000)) (hi := (160421153 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587002601197 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587002601197 / 500000000000) = 1/(500000000000 / 587002601197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1311 : Bounds (5013161 / 31250000) (160421153 / 1000000000) (Real.log (587002601197 / 500000000000)) := by
  have h := reflection_log_1311_neg
  have he : Real.log (587002601197 / 500000000000) = -Real.log (500000000000 / 587002601197) := by
    rw [show ((587002601197 / 500000000000) : ℝ) = ((500000000000 / 587002601197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1312_neg : (160843867 / 1000000000) ≤ -Real.log (500000000000 / 587250788529) ∧
    -Real.log (500000000000 / 587250788529) ≤ (40210967 / 250000000) := by
  have h := checkLog_sound (w := (87250788529 / 1087250788529)) (n := 12)
    (lo := (160843867 / 1000000000)) (hi := (40210967 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587250788529 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587250788529 / 500000000000) = 1/(500000000000 / 587250788529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1312 : Bounds (160843867 / 1000000000) (40210967 / 250000000) (Real.log (587250788529 / 500000000000)) := by
  have h := reflection_log_1312_neg
  have he : Real.log (587250788529 / 500000000000) = -Real.log (500000000000 / 587250788529) := by
    rw [show ((587250788529 / 500000000000) : ℝ) = ((500000000000 / 587250788529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1313_neg : (321747203 / 1000000000) ≤ -Real.log (12500000000 / 17244199881) ∧
    -Real.log (12500000000 / 17244199881) ≤ (80436801 / 250000000) := by
  have h := checkLog_sound (w := (4744199881 / 29744199881)) (n := 12)
    (lo := (321747203 / 1000000000)) (hi := (80436801 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17244199881 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17244199881 / 12500000000) = 1/(12500000000 / 17244199881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1313 : Bounds (321747203 / 1000000000) (80436801 / 250000000) (Real.log (17244199881 / 12500000000)) := by
  have h := reflection_log_1313_neg
  have he : Real.log (17244199881 / 12500000000) = -Real.log (12500000000 / 17244199881) := by
    rw [show ((17244199881 / 12500000000) : ℝ) = ((12500000000 / 17244199881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1314_neg : (80488107 / 250000000) ≤ -Real.log (500000000000 / 689909566873) ∧
    -Real.log (500000000000 / 689909566873) ≤ (321952429 / 1000000000) := by
  have h := checkLog_sound (w := (189909566873 / 1189909566873)) (n := 12)
    (lo := (80488107 / 250000000)) (hi := (321952429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((689909566873 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(689909566873 / 500000000000) = 1/(500000000000 / 689909566873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1314 : Bounds (80488107 / 250000000) (321952429 / 1000000000) (Real.log (689909566873 / 500000000000)) := by
  have h := reflection_log_1314_neg
  have he : Real.log (689909566873 / 500000000000) = -Real.log (500000000000 / 689909566873) := by
    rw [show ((689909566873 / 500000000000) : ℝ) = ((500000000000 / 689909566873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1315_neg : (2963227 / 20000000) ≤ -Real.log (10000 / 11597) ∧
    -Real.log (10000 / 11597) ≤ (148161351 / 1000000000) := by
  have h := checkLog_sound (w := (1597 / 21597)) (n := 12)
    (lo := (2963227 / 20000000)) (hi := (148161351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11597 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11597 / 10000) = 1/(10000 / 11597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1315 : Bounds (2963227 / 20000000) (148161351 / 1000000000) (Real.log (11597 / 10000)) := by
  have h := reflection_log_1315_neg
  have he : Real.log (11597 / 10000) = -Real.log (10000 / 11597) := by
    rw [show ((11597 / 10000) : ℝ) = ((10000 / 11597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1316_neg : (43499077 / 250000000) ≤ -Real.log (8403 / 10000) ∧
    -Real.log (8403 / 10000) ≤ (173996309 / 1000000000) := by
  have h := checkLog_sound (w := (1597 / 18403)) (n := 12)
    (lo := (43499077 / 250000000)) (hi := (173996309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8403) = 1/(8403 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1316 : Bounds (-173996309 / 1000000000) (-43499077 / 250000000) (Real.log (8403 / 10000)) := by
  have h := reflection_log_1316_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1317_neg : (159687 / 1000000000) ≤ -Real.log (10000000 / 10001597) ∧
    -Real.log (10000000 / 10001597) ≤ (19961 / 125000000) := by
  have h := checkLog_sound (w := (1597 / 20001597)) (n := 12)
    (lo := (159687 / 1000000000)) (hi := (19961 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001597 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001597 / 10000000) = 1/(10000000 / 10001597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1317 : Bounds (159687 / 1000000000) (19961 / 125000000) (Real.log (10001597 / 10000000)) := by
  have h := reflection_log_1317_neg
  have he : Real.log (10001597 / 10000000) = -Real.log (10000000 / 10001597) := by
    rw [show ((10001597 / 10000000) : ℝ) = ((10000000 / 10001597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1318_neg : (4991 / 31250000) ≤ -Real.log (9998403 / 10000000) ∧
    -Real.log (9998403 / 10000000) ≤ (159713 / 1000000000) := by
  have h := checkLog_sound (w := (1597 / 19998403)) (n := 12)
    (lo := (4991 / 31250000)) (hi := (159713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998403) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998403) = 1/(9998403 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1318 : Bounds (-159713 / 1000000000) (-4991 / 31250000) (Real.log (9998403 / 10000000)) := by
  have h := reflection_log_1318_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1319_neg : (15408689 / 200000000) ≤ -Real.log (1000000 / 1080089) ∧
    -Real.log (1000000 / 1080089) ≤ (38521723 / 500000000) := by
  have h := checkLog_sound (w := (80089 / 2080089)) (n := 12)
    (lo := (15408689 / 200000000)) (hi := (38521723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080089 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080089 / 1000000) = 1/(1000000 / 1080089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1319 : Bounds (15408689 / 200000000) (38521723 / 500000000) (Real.log (1080089 / 1000000)) := by
  have h := reflection_log_1319_neg
  have he : Real.log (1080089 / 1000000) = -Real.log (1000000 / 1080089) := by
    rw [show ((1080089 / 1000000) : ℝ) = ((1000000 / 1080089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1320_neg : (5217397 / 62500000) ≤ -Real.log (919911 / 1000000) ∧
    -Real.log (919911 / 1000000) ≤ (83478353 / 1000000000) := by
  have h := checkLog_sound (w := (80089 / 1919911)) (n := 12)
    (lo := (5217397 / 62500000)) (hi := (83478353 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919911) = 1/(919911 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1320 : Bounds (-83478353 / 1000000000) (-5217397 / 62500000) (Real.log (919911 / 1000000)) := by
  have h := reflection_log_1320_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1321_neg : (3861939 / 50000000) ≤ -Real.log (10000 / 10803) ∧
    -Real.log (10000 / 10803) ≤ (77238781 / 1000000000) := by
  have h := checkLog_sound (w := (803 / 20803)) (n := 12)
    (lo := (3861939 / 50000000)) (hi := (77238781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10803 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10803 / 10000) = 1/(10000 / 10803) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1321 : Bounds (3861939 / 50000000) (77238781 / 1000000000) (Real.log (10803 / 10000)) := by
  have h := reflection_log_1321_neg
  have he : Real.log (10803 / 10000) = -Real.log (10000 / 10803) := by
    rw [show ((10803 / 10000) : ℝ) = ((10000 / 10803) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1322_neg : (83707749 / 1000000000) ≤ -Real.log (9197 / 10000) ∧
    -Real.log (9197 / 10000) ≤ (334831 / 4000000) := by
  have h := checkLog_sound (w := (803 / 19197)) (n := 12)
    (lo := (83707749 / 1000000000)) (hi := (334831 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 9197) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 9197) = 1/(9197 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1322 : Bounds (-334831 / 4000000) (-83707749 / 1000000000) (Real.log (9197 / 10000)) := by
  have h := reflection_log_1322_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1323_neg : (808621 / 125000000) ≤ -Real.log (99355191 / 100000000) ∧
    -Real.log (99355191 / 100000000) ≤ (6468969 / 1000000000) := by
  have h := checkLog_sound (w := (644809 / 199355191)) (n := 12)
    (lo := (808621 / 125000000)) (hi := (6468969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000000 / 99355191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000000 / 99355191) = 1/(99355191 / 100000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1323 : Bounds (-6468969 / 1000000000) (-808621 / 125000000) (Real.log (99355191 / 100000000)) := by
  have h := reflection_log_1323_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1324_neg : (6434907 / 1000000000) ≤ -Real.log (993585752079 / 1000000000000) ∧
    -Real.log (993585752079 / 1000000000000) ≤ (1608727 / 250000000) := by
  have h := checkLog_sound (w := (6414247921 / 1993585752079)) (n := 12)
    (lo := (6434907 / 1000000000)) (hi := (1608727 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993585752079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993585752079) = 1/(993585752079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1324 : Bounds (-1608727 / 250000000) (-6434907 / 1000000000) (Real.log (993585752079 / 1000000000000)) := by
  have h := reflection_log_1324_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1325_neg : (160521797 / 1000000000) ≤ -Real.log (500000000000 / 587061683141) ∧
    -Real.log (500000000000 / 587061683141) ≤ (80260899 / 500000000) := by
  have h := checkLog_sound (w := (87061683141 / 1087061683141)) (n := 12)
    (lo := (160521797 / 1000000000)) (hi := (80260899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587061683141 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587061683141 / 500000000000) = 1/(500000000000 / 587061683141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1325 : Bounds (160521797 / 1000000000) (80260899 / 500000000) (Real.log (587061683141 / 500000000000)) := by
  have h := reflection_log_1325_neg
  have he : Real.log (587061683141 / 500000000000) = -Real.log (500000000000 / 587061683141) := by
    rw [show ((587061683141 / 500000000000) : ℝ) = ((500000000000 / 587061683141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1326_neg : (160946529 / 1000000000) ≤ -Real.log (5000000000 / 5873110797) ∧
    -Real.log (5000000000 / 5873110797) ≤ (16094653 / 100000000) := by
  have h := checkLog_sound (w := (873110797 / 10873110797)) (n := 12)
    (lo := (160946529 / 1000000000)) (hi := (16094653 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5873110797 / 5000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5873110797 / 5000000000) = 1/(5000000000 / 5873110797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1326 : Bounds (160946529 / 1000000000) (16094653 / 100000000) (Real.log (5873110797 / 5000000000)) := by
  have h := reflection_log_1326_neg
  have he : Real.log (5873110797 / 5000000000) = -Real.log (5000000000 / 5873110797) := by
    rw [show ((5873110797 / 5000000000) : ℝ) = ((5000000000 / 5873110797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1327_neg : (80488107 / 250000000) ≤ -Real.log (62500000000 / 86238695859) ∧
    -Real.log (62500000000 / 86238695859) ≤ (321952429 / 1000000000) := by
  have h := checkLog_sound (w := (23738695859 / 148738695859)) (n := 12)
    (lo := (80488107 / 250000000)) (hi := (321952429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86238695859 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86238695859 / 62500000000) = 1/(62500000000 / 86238695859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1327 : Bounds (80488107 / 250000000) (321952429 / 1000000000) (Real.log (86238695859 / 62500000000)) := by
  have h := reflection_log_1327_neg
  have he : Real.log (86238695859 / 62500000000) = -Real.log (62500000000 / 86238695859) := by
    rw [show ((86238695859 / 62500000000) : ℝ) = ((62500000000 / 86238695859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1328_neg : (322157659 / 1000000000) ≤ -Real.log (500000000000 / 690051172201) ∧
    -Real.log (500000000000 / 690051172201) ≤ (16107883 / 50000000) := by
  have h := checkLog_sound (w := (190051172201 / 1190051172201)) (n := 12)
    (lo := (322157659 / 1000000000)) (hi := (16107883 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((690051172201 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(690051172201 / 500000000000) = 1/(500000000000 / 690051172201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1328 : Bounds (322157659 / 1000000000) (16107883 / 50000000) (Real.log (690051172201 / 500000000000)) := by
  have h := reflection_log_1328_neg
  have he : Real.log (690051172201 / 500000000000) = -Real.log (500000000000 / 690051172201) := by
    rw [show ((690051172201 / 500000000000) : ℝ) = ((500000000000 / 690051172201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1329_neg : (18530947 / 125000000) ≤ -Real.log (5000 / 5799) ∧
    -Real.log (5000 / 5799) ≤ (148247577 / 1000000000) := by
  have h := checkLog_sound (w := (799 / 10799)) (n := 12)
    (lo := (18530947 / 125000000)) (hi := (148247577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5799 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5799 / 5000) = 1/(5000 / 5799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1329 : Bounds (18530947 / 125000000) (148247577 / 1000000000) (Real.log (5799 / 5000)) := by
  have h := reflection_log_1329_neg
  have he : Real.log (5799 / 5000) = -Real.log (5000 / 5799) := by
    rw [show ((5799 / 5000) : ℝ) = ((5000 / 5799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1330_neg : (4352883 / 25000000) ≤ -Real.log (4201 / 5000) ∧
    -Real.log (4201 / 5000) ≤ (174115321 / 1000000000) := by
  have h := checkLog_sound (w := (799 / 9201)) (n := 12)
    (lo := (4352883 / 25000000)) (hi := (174115321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4201) = 1/(4201 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1330 : Bounds (-174115321 / 1000000000) (-4352883 / 25000000) (Real.log (4201 / 5000)) := by
  have h := reflection_log_1330_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1331_neg : (159787 / 1000000000) ≤ -Real.log (5000000 / 5000799) ∧
    -Real.log (5000000 / 5000799) ≤ (39947 / 250000000) := by
  have h := checkLog_sound (w := (799 / 10000799)) (n := 12)
    (lo := (159787 / 1000000000)) (hi := (39947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000799 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000799 / 5000000) = 1/(5000000 / 5000799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1331 : Bounds (159787 / 1000000000) (39947 / 250000000) (Real.log (5000799 / 5000000)) := by
  have h := reflection_log_1331_neg
  have he : Real.log (5000799 / 5000000) = -Real.log (5000000 / 5000799) := by
    rw [show ((5000799 / 5000000) : ℝ) = ((5000000 / 5000799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1332_neg : (39953 / 250000000) ≤ -Real.log (4999201 / 5000000) ∧
    -Real.log (4999201 / 5000000) ≤ (159813 / 1000000000) := by
  have h := checkLog_sound (w := (799 / 9999201)) (n := 12)
    (lo := (39953 / 250000000)) (hi := (159813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999201) = 1/(4999201 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1332 : Bounds (-159813 / 1000000000) (-39953 / 250000000) (Real.log (4999201 / 5000000)) := by
  have h := reflection_log_1332_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1333_neg : (38545331 / 500000000) ≤ -Real.log (50000 / 54007) ∧
    -Real.log (50000 / 54007) ≤ (77090663 / 1000000000) := by
  have h := checkLog_sound (w := (4007 / 104007)) (n := 12)
    (lo := (38545331 / 500000000)) (hi := (77090663 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54007 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54007 / 50000) = 1/(50000 / 54007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1333 : Bounds (38545331 / 500000000) (77090663 / 1000000000) (Real.log (54007 / 50000)) := by
  have h := reflection_log_1333_neg
  have he : Real.log (54007 / 50000) = -Real.log (50000 / 54007) := by
    rw [show ((54007 / 50000) : ℝ) = ((50000 / 54007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1334_neg : (41766897 / 500000000) ≤ -Real.log (45993 / 50000) ∧
    -Real.log (45993 / 50000) ≤ (16706759 / 200000000) := by
  have h := checkLog_sound (w := (4007 / 95993)) (n := 12)
    (lo := (41766897 / 500000000)) (hi := (16706759 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45993) = 1/(45993 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1334 : Bounds (-16706759 / 200000000) (-41766897 / 500000000) (Real.log (45993 / 50000)) := by
  have h := reflection_log_1334_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1335_neg : (19321497 / 250000000) ≤ -Real.log (1000000 / 1080351) ∧
    -Real.log (1000000 / 1080351) ≤ (77285989 / 1000000000) := by
  have h := checkLog_sound (w := (80351 / 2080351)) (n := 12)
    (lo := (19321497 / 250000000)) (hi := (77285989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080351 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080351 / 1000000) = 1/(1000000 / 1080351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1335 : Bounds (19321497 / 250000000) (77285989 / 1000000000) (Real.log (1080351 / 1000000)) := by
  have h := reflection_log_1335_neg
  have he : Real.log (1080351 / 1000000) = -Real.log (1000000 / 1080351) := by
    rw [show ((1080351 / 1000000) : ℝ) = ((1000000 / 1080351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1336_neg : (83763203 / 1000000000) ≤ -Real.log (919649 / 1000000) ∧
    -Real.log (919649 / 1000000) ≤ (20940801 / 250000000) := by
  have h := checkLog_sound (w := (80351 / 1919649)) (n := 12)
    (lo := (83763203 / 1000000000)) (hi := (20940801 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919649) = 1/(919649 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1336 : Bounds (-20940801 / 250000000) (-83763203 / 1000000000) (Real.log (919649 / 1000000)) := by
  have h := reflection_log_1336_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1337_neg : (1295443 / 200000000) ≤ -Real.log (993543716799 / 1000000000000) ∧
    -Real.log (993543716799 / 1000000000000) ≤ (202413 / 31250000) := by
  have h := checkLog_sound (w := (6456283201 / 1993543716799)) (n := 12)
    (lo := (1295443 / 200000000)) (hi := (202413 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993543716799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993543716799) = 1/(993543716799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1337 : Bounds (-202413 / 31250000) (-1295443 / 200000000) (Real.log (993543716799 / 1000000000000)) := by
  have h := reflection_log_1337_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1338_neg : (1610783 / 250000000) ≤ -Real.log (2483943951 / 2500000000) ∧
    -Real.log (2483943951 / 2500000000) ≤ (6443133 / 1000000000) := by
  have h := checkLog_sound (w := (16056049 / 4983943951)) (n := 12)
    (lo := (1610783 / 250000000)) (hi := (6443133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2483943951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2483943951) = 1/(2483943951 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1338 : Bounds (-6443133 / 1000000000) (-1610783 / 250000000) (Real.log (2483943951 / 2500000000)) := by
  have h := reflection_log_1338_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1339_neg : (20078057 / 125000000) ≤ -Real.log (25000000000 / 29356097667) ∧
    -Real.log (25000000000 / 29356097667) ≤ (160624457 / 1000000000) := by
  have h := checkLog_sound (w := (4356097667 / 54356097667)) (n := 12)
    (lo := (20078057 / 125000000)) (hi := (160624457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29356097667 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29356097667 / 25000000000) = 1/(25000000000 / 29356097667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1339 : Bounds (20078057 / 125000000) (160624457 / 1000000000) (Real.log (29356097667 / 25000000000)) := by
  have h := reflection_log_1339_neg
  have he : Real.log (29356097667 / 25000000000) = -Real.log (25000000000 / 29356097667) := by
    rw [show ((29356097667 / 25000000000) : ℝ) = ((25000000000 / 29356097667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1340_neg : (161049191 / 1000000000) ≤ -Real.log (500000000000 / 587371377559) ∧
    -Real.log (500000000000 / 587371377559) ≤ (20131149 / 125000000) := by
  have h := checkLog_sound (w := (87371377559 / 1087371377559)) (n := 12)
    (lo := (161049191 / 1000000000)) (hi := (20131149 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587371377559 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587371377559 / 500000000000) = 1/(500000000000 / 587371377559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1340 : Bounds (161049191 / 1000000000) (20131149 / 125000000) (Real.log (587371377559 / 500000000000)) := by
  have h := reflection_log_1340_neg
  have he : Real.log (587371377559 / 500000000000) = -Real.log (500000000000 / 587371377559) := by
    rw [show ((587371377559 / 500000000000) : ℝ) = ((500000000000 / 587371377559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1341_neg : (322157659 / 1000000000) ≤ -Real.log (2500000000 / 3450255861) ∧
    -Real.log (2500000000 / 3450255861) ≤ (16107883 / 50000000) := by
  have h := checkLog_sound (w := (950255861 / 5950255861)) (n := 12)
    (lo := (322157659 / 1000000000)) (hi := (16107883 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3450255861 / 2500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3450255861 / 2500000000) = 1/(2500000000 / 3450255861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1341 : Bounds (322157659 / 1000000000) (16107883 / 50000000) (Real.log (3450255861 / 2500000000)) := by
  have h := reflection_log_1341_neg
  have he : Real.log (3450255861 / 2500000000) = -Real.log (2500000000 / 3450255861) := by
    rw [show ((3450255861 / 2500000000) : ℝ) = ((2500000000 / 3450255861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1342_neg : (20147681 / 62500000) ≤ -Real.log (125000000000 / 172548202809) ∧
    -Real.log (125000000000 / 172548202809) ≤ (322362897 / 1000000000) := by
  have h := checkLog_sound (w := (47548202809 / 297548202809)) (n := 12)
    (lo := (20147681 / 62500000)) (hi := (322362897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172548202809 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172548202809 / 125000000000) = 1/(125000000000 / 172548202809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1342 : Bounds (20147681 / 62500000) (322362897 / 1000000000) (Real.log (172548202809 / 125000000000)) := by
  have h := reflection_log_1342_neg
  have he : Real.log (172548202809 / 125000000000) = -Real.log (125000000000 / 172548202809) := by
    rw [show ((172548202809 / 125000000000) : ℝ) = ((125000000000 / 172548202809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1343_neg : (74166897 / 500000000) ≤ -Real.log (10000 / 11599) ∧
    -Real.log (10000 / 11599) ≤ (29666759 / 200000000) := by
  have h := checkLog_sound (w := (1599 / 21599)) (n := 12)
    (lo := (74166897 / 500000000)) (hi := (29666759 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11599 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11599 / 10000) = 1/(10000 / 11599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1343 : Bounds (74166897 / 500000000) (29666759 / 200000000) (Real.log (11599 / 10000)) := by
  have h := reflection_log_1343_neg
  have he : Real.log (11599 / 10000) = -Real.log (10000 / 11599) := by
    rw [show ((11599 / 10000) : ℝ) = ((10000 / 11599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
