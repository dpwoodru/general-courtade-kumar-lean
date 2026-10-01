import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_13312_neg : (61653937 / 200000000) ≤ -Real.log (250000 / 340267) ∧
    -Real.log (250000 / 340267) ≤ (154134843 / 500000000) := by
  have h := checkLog_sound (w := (90267 / 590267)) (n := 12)
    (lo := (61653937 / 200000000)) (hi := (154134843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340267 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340267 / 250000) = 1/(250000 / 340267) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13312 : Bounds (61653937 / 200000000) (154134843 / 500000000) (Real.log (340267 / 250000)) := by
  have h := reflection_log_13312_neg
  have he : Real.log (340267 / 250000) = -Real.log (250000 / 340267) := by
    rw [show ((340267 / 250000) : ℝ) = ((250000 / 340267) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13313_neg : (223978623 / 500000000) ≤ -Real.log (159733 / 250000) ∧
    -Real.log (159733 / 250000) ≤ (447957247 / 1000000000) := by
  have h := checkLog_sound (w := (90267 / 409733)) (n := 12)
    (lo := (223978623 / 500000000)) (hi := (447957247 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 159733) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 159733) = 1/(159733 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13313 : Bounds (-447957247 / 1000000000) (-223978623 / 500000000) (Real.log (159733 / 250000)) := by
  have h := reflection_log_13313_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13314_neg : (155074397 / 500000000) ≤ -Real.log (250000 / 340907) ∧
    -Real.log (250000 / 340907) ≤ (62029759 / 200000000) := by
  have h := checkLog_sound (w := (90907 / 590907)) (n := 12)
    (lo := (155074397 / 500000000)) (hi := (62029759 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((340907 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(340907 / 250000) = 1/(250000 / 340907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13314 : Bounds (155074397 / 500000000) (62029759 / 200000000) (Real.log (340907 / 250000)) := by
  have h := reflection_log_13314_neg
  have he : Real.log (340907 / 250000) = -Real.log (250000 / 340907) := by
    rw [show ((340907 / 250000) : ℝ) = ((250000 / 340907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13315_neg : (22598599 / 50000000) ≤ -Real.log (159093 / 250000) ∧
    -Real.log (159093 / 250000) ≤ (451971981 / 1000000000) := by
  have h := checkLog_sound (w := (90907 / 409093)) (n := 12)
    (lo := (22598599 / 50000000)) (hi := (451971981 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 159093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 159093) = 1/(159093 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13315 : Bounds (-451971981 / 1000000000) (-22598599 / 50000000) (Real.log (159093 / 250000)) := by
  have h := reflection_log_13315_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13316_neg : (70911593 / 500000000) ≤ -Real.log (54235917351 / 62500000000) ∧
    -Real.log (54235917351 / 62500000000) ≤ (141823187 / 1000000000) := by
  have h := checkLog_sound (w := (8264082649 / 116735917351)) (n := 12)
    (lo := (70911593 / 500000000)) (hi := (141823187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 54235917351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 54235917351) = 1/(54235917351 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13316 : Bounds (-141823187 / 1000000000) (-70911593 / 500000000) (Real.log (54235917351 / 62500000000)) := by
  have h := reflection_log_13316_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13317_neg : (3492189 / 25000000) ≤ -Real.log (54351868711 / 62500000000) ∧
    -Real.log (54351868711 / 62500000000) ≤ (139687561 / 1000000000) := by
  have h := checkLog_sound (w := (8148131289 / 116851868711)) (n := 12)
    (lo := (3492189 / 25000000)) (hi := (139687561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 54351868711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 54351868711) = 1/(54351868711 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13317 : Bounds (-139687561 / 1000000000) (-3492189 / 25000000) (Real.log (54351868711 / 62500000000)) := by
  have h := reflection_log_13317_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13318_neg : (756226931 / 1000000000) ≤ -Real.log (500000000000 / 1065111780283) ∧
    -Real.log (500000000000 / 1065111780283) ≤ (756226933 / 1000000000) := by
  have h := checkLog_sound (w := (65111780283 / 2065111780283)) (n := 12)
    (lo := (63079751 / 1000000000)) (hi := (7884969 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1065111780283 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1065111780283 / 1000000000000) = 1/(500000000000 / 1065111780283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13318 : Bounds (756226931 / 1000000000) (756226933 / 1000000000) (Real.log (1065111780283 / 500000000000)) := by
  have h := reflection_log_13318_neg
  have he : Real.log (1065111780283 / 500000000000) = -Real.log (500000000000 / 1065111780283) := by
    rw [show ((1065111780283 / 500000000000) : ℝ) = ((500000000000 / 1065111780283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13319_neg : (30484831 / 40000000) ≤ -Real.log (500000000000 / 1071407918639) ∧
    -Real.log (500000000000 / 1071407918639) ≤ (762120777 / 1000000000) := by
  have h := checkLog_sound (w := (71407918639 / 2071407918639)) (n := 12)
    (lo := (13794719 / 200000000)) (hi := (17243399 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1071407918639 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1071407918639 / 1000000000000) = 1/(500000000000 / 1071407918639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13319 : Bounds (30484831 / 40000000) (762120777 / 1000000000) (Real.log (1071407918639 / 500000000000)) := by
  have h := reflection_log_13319_neg
  have he : Real.log (1071407918639 / 500000000000) = -Real.log (500000000000 / 1071407918639) := by
    rw [show ((1071407918639 / 500000000000) : ℝ) = ((500000000000 / 1071407918639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13320_neg : (796365539 / 500000000) ≤ -Real.log (62500000000 / 307322485207) ∧
    -Real.log (62500000000 / 307322485207) ≤ (1592731081 / 1000000000) := by
  have h := checkLog_sound (w := (57322485207 / 557322485207)) (n := 12)
    (lo := (103218359 / 500000000)) (hi := (206436719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((307322485207 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(307322485207 / 250000000000) = 1/(62500000000 / 307322485207) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13320 : Bounds (796365539 / 500000000) (1592731081 / 1000000000) (Real.log (307322485207 / 62500000000)) := by
  have h := reflection_log_13320_neg
  have he : Real.log (307322485207 / 62500000000) = -Real.log (62500000000 / 307322485207) := by
    rw [show ((307322485207 / 62500000000) : ℝ) = ((62500000000 / 307322485207) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13321_neg : (1603449869 / 1000000000) ≤ -Real.log (250000000000 / 1242537313433) ∧
    -Real.log (250000000000 / 1242537313433) ≤ (100215617 / 62500000) := by
  have h := checkLog_sound (w := (242537313433 / 2242537313433)) (n := 12)
    (lo := (217155509 / 1000000000)) (hi := (21715551 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1242537313433 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1242537313433 / 1000000000000) = 1/(250000000000 / 1242537313433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13321 : Bounds (1603449869 / 1000000000) (100215617 / 62500000) (Real.log (1242537313433 / 250000000000)) := by
  have h := reflection_log_13321_neg
  have he : Real.log (1242537313433 / 250000000000) = -Real.log (250000000000 / 1242537313433) := by
    rw [show ((1242537313433 / 250000000000) : ℝ) = ((250000000000 / 1242537313433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13322_neg : (511625303 / 1000000000) ≤ -Real.log (250 / 417) ∧
    -Real.log (250 / 417) ≤ (63953163 / 125000000) := by
  have h := checkLog_sound (w := (167 / 667)) (n := 12)
    (lo := (511625303 / 1000000000)) (hi := (63953163 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((417 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(417 / 250) = 1/(250 / 417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13322 : Bounds (511625303 / 1000000000) (63953163 / 125000000) (Real.log (417 / 250)) := by
  have h := reflection_log_13322_neg
  have he : Real.log (417 / 250) = -Real.log (250 / 417) := by
    rw [show ((417 / 250) : ℝ) = ((250 / 417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13323_neg : (1102620309 / 1000000000) ≤ -Real.log (83 / 250) ∧
    -Real.log (83 / 250) ≤ (1102620311 / 1000000000) := by
  have h := checkLog_sound (w := (21 / 104)) (n := 12)
    (lo := (409473129 / 1000000000)) (hi := (40947313 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 83) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125 / 83) = 1/(83 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13323 : Bounds (-1102620311 / 1000000000) (-1102620309 / 1000000000) (Real.log (83 / 250)) := by
  have h := reflection_log_13323_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13324_neg : (5217 / 7812500) ≤ -Real.log (250000 / 250167) ∧
    -Real.log (250000 / 250167) ≤ (667777 / 1000000000) := by
  have h := checkLog_sound (w := (167 / 500167)) (n := 12)
    (lo := (5217 / 7812500)) (hi := (667777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250167 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250167 / 250000) = 1/(250000 / 250167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13324 : Bounds (5217 / 7812500) (667777 / 1000000000) (Real.log (250167 / 250000)) := by
  have h := reflection_log_13324_neg
  have he : Real.log (250167 / 250000) = -Real.log (250000 / 250167) := by
    rw [show ((250167 / 250000) : ℝ) = ((250000 / 250167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13325_neg : (668223 / 1000000000) ≤ -Real.log (249833 / 250000) ∧
    -Real.log (249833 / 250000) ≤ (10441 / 15625000) := by
  have h := checkLog_sound (w := (167 / 499833)) (n := 12)
    (lo := (668223 / 1000000000)) (hi := (10441 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249833) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249833) = 1/(249833 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13325 : Bounds (-10441 / 15625000) (-668223 / 1000000000) (Real.log (249833 / 250000)) := by
  have h := reflection_log_13325_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13326_neg : (19356931 / 62500000) ≤ -Real.log (1000000 / 1363031) ∧
    -Real.log (1000000 / 1363031) ≤ (309710897 / 1000000000) := by
  have h := checkLog_sound (w := (363031 / 2363031)) (n := 12)
    (lo := (19356931 / 62500000)) (hi := (309710897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1363031 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1363031 / 1000000) = 1/(1000000 / 1363031) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13326 : Bounds (19356931 / 62500000) (309710897 / 1000000000) (Real.log (1363031 / 1000000)) := by
  have h := reflection_log_13326_neg
  have he : Real.log (1363031 / 1000000) = -Real.log (1000000 / 1363031) := by
    rw [show ((1363031 / 1000000) : ℝ) = ((1000000 / 1363031) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13327_neg : (45103429 / 100000000) ≤ -Real.log (636969 / 1000000) ∧
    -Real.log (636969 / 1000000) ≤ (451034291 / 1000000000) := by
  have h := checkLog_sound (w := (363031 / 1636969)) (n := 12)
    (lo := (45103429 / 100000000)) (hi := (451034291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 636969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 636969) = 1/(636969 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13327 : Bounds (-451034291 / 1000000000) (-45103429 / 100000000) (Real.log (636969 / 1000000)) := by
  have h := reflection_log_13327_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13328_neg : (7789829 / 25000000) ≤ -Real.log (1000000 / 1365599) ∧
    -Real.log (1000000 / 1365599) ≤ (311593161 / 1000000000) := by
  have h := checkLog_sound (w := (365599 / 2365599)) (n := 12)
    (lo := (7789829 / 25000000)) (hi := (311593161 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1365599 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1365599 / 1000000) = 1/(1000000 / 1365599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13328 : Bounds (7789829 / 25000000) (311593161 / 1000000000) (Real.log (1365599 / 1000000)) := by
  have h := reflection_log_13328_neg
  have he : Real.log (1365599 / 1000000) = -Real.log (1000000 / 1365599) := by
    rw [show ((1365599 / 1000000) : ℝ) = ((1000000 / 1365599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13329_neg : (28442127 / 62500000) ≤ -Real.log (634401 / 1000000) ∧
    -Real.log (634401 / 1000000) ≤ (455074033 / 1000000000) := by
  have h := checkLog_sound (w := (365599 / 1634401)) (n := 12)
    (lo := (28442127 / 62500000)) (hi := (455074033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 634401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 634401) = 1/(634401 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13329 : Bounds (-455074033 / 1000000000) (-28442127 / 62500000) (Real.log (634401 / 1000000)) := by
  have h := reflection_log_13329_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13330_neg : (17935109 / 125000000) ≤ -Real.log (866337371199 / 1000000000000) ∧
    -Real.log (866337371199 / 1000000000000) ≤ (143480873 / 1000000000) := by
  have h := checkLog_sound (w := (133662628801 / 1866337371199)) (n := 12)
    (lo := (17935109 / 125000000)) (hi := (143480873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 866337371199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 866337371199) = 1/(866337371199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13330 : Bounds (-143480873 / 1000000000) (-17935109 / 125000000) (Real.log (866337371199 / 1000000000000)) := by
  have h := reflection_log_13330_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13331_neg : (141323393 / 1000000000) ≤ -Real.log (868208493039 / 1000000000000) ∧
    -Real.log (868208493039 / 1000000000000) ≤ (70661697 / 500000000) := by
  have h := checkLog_sound (w := (131791506961 / 1868208493039)) (n := 12)
    (lo := (141323393 / 1000000000)) (hi := (70661697 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 868208493039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 868208493039) = 1/(868208493039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13331 : Bounds (-70661697 / 500000000) (-141323393 / 1000000000) (Real.log (868208493039 / 1000000000000)) := by
  have h := reflection_log_13331_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13332_neg : (380372593 / 500000000) ≤ -Real.log (500000000000 / 1069935114581) ∧
    -Real.log (500000000000 / 1069935114581) ≤ (190186297 / 250000000) := by
  have h := checkLog_sound (w := (69935114581 / 2069935114581)) (n := 12)
    (lo := (33799003 / 500000000)) (hi := (67598007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1069935114581 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1069935114581 / 1000000000000) = 1/(500000000000 / 1069935114581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13332 : Bounds (380372593 / 500000000) (190186297 / 250000000) (Real.log (1069935114581 / 500000000000)) := by
  have h := reflection_log_13332_neg
  have he : Real.log (1069935114581 / 500000000000) = -Real.log (500000000000 / 1069935114581) := by
    rw [show ((1069935114581 / 500000000000) : ℝ) = ((500000000000 / 1069935114581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13333_neg : (95833399 / 125000000) ≤ -Real.log (100000000000 / 215258015041) ∧
    -Real.log (100000000000 / 215258015041) ≤ (383333597 / 500000000) := by
  have h := checkLog_sound (w := (15258015041 / 415258015041)) (n := 12)
    (lo := (18380003 / 250000000)) (hi := (73520013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215258015041 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(215258015041 / 200000000000) = 1/(100000000000 / 215258015041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13333 : Bounds (95833399 / 125000000) (383333597 / 500000000) (Real.log (215258015041 / 100000000000)) := by
  have h := reflection_log_13333_neg
  have he : Real.log (215258015041 / 100000000000) = -Real.log (100000000000 / 215258015041) := by
    rw [show ((215258015041 / 100000000000) : ℝ) = ((100000000000 / 215258015041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13334_neg : (1603449869 / 1000000000) ≤ -Real.log (100000000000 / 497014925373) ∧
    -Real.log (100000000000 / 497014925373) ≤ (100215617 / 62500000) := by
  have h := checkLog_sound (w := (97014925373 / 897014925373)) (n := 12)
    (lo := (217155509 / 1000000000)) (hi := (21715551 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((497014925373 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(497014925373 / 400000000000) = 1/(100000000000 / 497014925373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13334 : Bounds (1603449869 / 1000000000) (100215617 / 62500000) (Real.log (497014925373 / 100000000000)) := by
  have h := reflection_log_13334_neg
  have he : Real.log (497014925373 / 100000000000) = -Real.log (100000000000 / 497014925373) := by
    rw [show ((497014925373 / 100000000000) : ℝ) = ((100000000000 / 497014925373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13335_neg : (403561403 / 250000000) ≤ -Real.log (125000000000 / 628012048193) ∧
    -Real.log (125000000000 / 628012048193) ≤ (322849123 / 200000000) := by
  have h := checkLog_sound (w := (128012048193 / 1128012048193)) (n := 12)
    (lo := (56987813 / 250000000)) (hi := (227951253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((628012048193 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(628012048193 / 500000000000) = 1/(125000000000 / 628012048193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13335 : Bounds (403561403 / 250000000) (322849123 / 200000000) (Real.log (628012048193 / 125000000000)) := by
  have h := reflection_log_13335_neg
  have he : Real.log (628012048193 / 125000000000) = -Real.log (125000000000 / 628012048193) := by
    rw [show ((628012048193 / 125000000000) : ℝ) = ((125000000000 / 628012048193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13336_neg : (513422249 / 1000000000) ≤ -Real.log (1000 / 1671) ∧
    -Real.log (1000 / 1671) ≤ (2053689 / 4000000) := by
  have h := checkLog_sound (w := (671 / 2671)) (n := 12)
    (lo := (513422249 / 1000000000)) (hi := (2053689 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1671 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1671 / 1000) = 1/(1000 / 1671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13336 : Bounds (513422249 / 1000000000) (2053689 / 4000000) (Real.log (1671 / 1000)) := by
  have h := reflection_log_13336_neg
  have he : Real.log (1671 / 1000) = -Real.log (1000 / 1671) := by
    rw [show ((1671 / 1000) : ℝ) = ((1000 / 1671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13337_neg : (1111697527 / 1000000000) ≤ -Real.log (329 / 1000) ∧
    -Real.log (329 / 1000) ≤ (1111697529 / 1000000000) := by
  have h := checkLog_sound (w := (171 / 829)) (n := 12)
    (lo := (418550347 / 1000000000)) (hi := (104637587 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 329) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 329) = 1/(329 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13337 : Bounds (-1111697529 / 1000000000) (-1111697527 / 1000000000) (Real.log (329 / 1000)) := by
  have h := reflection_log_13337_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13338_neg : (335387 / 500000000) ≤ -Real.log (1000000 / 1000671) ∧
    -Real.log (1000000 / 1000671) ≤ (26831 / 40000000) := by
  have h := checkLog_sound (w := (671 / 2000671)) (n := 12)
    (lo := (335387 / 500000000)) (hi := (26831 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000671 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000671 / 1000000) = 1/(1000000 / 1000671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13338 : Bounds (335387 / 500000000) (26831 / 40000000) (Real.log (1000671 / 1000000)) := by
  have h := reflection_log_13338_neg
  have he : Real.log (1000671 / 1000000) = -Real.log (1000000 / 1000671) := by
    rw [show ((1000671 / 1000000) : ℝ) = ((1000000 / 1000671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13339_neg : (26849 / 40000000) ≤ -Real.log (999329 / 1000000) ∧
    -Real.log (999329 / 1000000) ≤ (335613 / 500000000) := by
  have h := checkLog_sound (w := (671 / 1999329)) (n := 12)
    (lo := (26849 / 40000000)) (hi := (335613 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999329) = 1/(999329 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13339 : Bounds (-335613 / 500000000) (-26849 / 40000000) (Real.log (999329 / 1000000)) := by
  have h := reflection_log_13339_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13340_neg : (311155161 / 1000000000) ≤ -Real.log (1000000 / 1365001) ∧
    -Real.log (1000000 / 1365001) ≤ (155577581 / 500000000) := by
  have h := checkLog_sound (w := (365001 / 2365001)) (n := 12)
    (lo := (311155161 / 1000000000)) (hi := (155577581 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1365001 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1365001 / 1000000) = 1/(1000000 / 1365001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13340 : Bounds (311155161 / 1000000000) (155577581 / 500000000) (Real.log (1365001 / 1000000)) := by
  have h := reflection_log_13340_neg
  have he : Real.log (1365001 / 1000000) = -Real.log (1000000 / 1365001) := by
    rw [show ((1365001 / 1000000) : ℝ) = ((1000000 / 1365001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13341_neg : (227065927 / 500000000) ≤ -Real.log (634999 / 1000000) ∧
    -Real.log (634999 / 1000000) ≤ (90826371 / 200000000) := by
  have h := checkLog_sound (w := (365001 / 1634999)) (n := 12)
    (lo := (227065927 / 500000000)) (hi := (90826371 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 634999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 634999) = 1/(634999 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13341 : Bounds (-90826371 / 200000000) (-227065927 / 500000000) (Real.log (634999 / 1000000)) := by
  have h := reflection_log_13341_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13342_neg : (156519549 / 500000000) ≤ -Real.log (40000 / 54703) ∧
    -Real.log (40000 / 54703) ≤ (313039099 / 1000000000) := by
  have h := checkLog_sound (w := (14703 / 94703)) (n := 12)
    (lo := (156519549 / 500000000)) (hi := (313039099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54703 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54703 / 40000) = 1/(40000 / 54703) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13342 : Bounds (156519549 / 500000000) (313039099 / 1000000000) (Real.log (54703 / 40000)) := by
  have h := reflection_log_13342_neg
  have he : Real.log (54703 / 40000) = -Real.log (40000 / 54703) := by
    rw [show ((54703 / 40000) : ℝ) = ((40000 / 54703) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13343_neg : (229096821 / 500000000) ≤ -Real.log (25297 / 40000) ∧
    -Real.log (25297 / 40000) ≤ (458193643 / 1000000000) := by
  have h := checkLog_sound (w := (14703 / 65297)) (n := 12)
    (lo := (229096821 / 500000000)) (hi := (458193643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 25297) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 25297) = 1/(25297 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13343 : Bounds (-458193643 / 1000000000) (-229096821 / 500000000) (Real.log (25297 / 40000)) := by
  have h := reflection_log_13343_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13344_neg : (9072159 / 62500000) ≤ -Real.log (1383821791 / 1600000000) ∧
    -Real.log (1383821791 / 1600000000) ≤ (29030909 / 200000000) := by
  have h := checkLog_sound (w := (216178209 / 2983821791)) (n := 12)
    (lo := (9072159 / 62500000)) (hi := (29030909 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1383821791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1383821791) = 1/(1383821791 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13344 : Bounds (-29030909 / 200000000) (-9072159 / 62500000) (Real.log (1383821791 / 1600000000)) := by
  have h := reflection_log_13344_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13345_neg : (142976693 / 1000000000) ≤ -Real.log (866774269999 / 1000000000000) ∧
    -Real.log (866774269999 / 1000000000000) ≤ (71488347 / 500000000) := by
  have h := checkLog_sound (w := (133225730001 / 1866774269999)) (n := 12)
    (lo := (142976693 / 1000000000)) (hi := (71488347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 866774269999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 866774269999) = 1/(866774269999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13345 : Bounds (-71488347 / 500000000) (-142976693 / 1000000000) (Real.log (866774269999 / 1000000000000)) := by
  have h := reflection_log_13345_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13346_neg : (153057403 / 200000000) ≤ -Real.log (100000000000 / 214961125923) ∧
    -Real.log (100000000000 / 214961125923) ≤ (765287017 / 1000000000) := by
  have h := checkLog_sound (w := (14961125923 / 414961125923)) (n := 12)
    (lo := (14427967 / 200000000)) (hi := (18034959 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((214961125923 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(214961125923 / 200000000000) = 1/(100000000000 / 214961125923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13346 : Bounds (153057403 / 200000000) (765287017 / 1000000000) (Real.log (214961125923 / 100000000000)) := by
  have h := reflection_log_13346_neg
  have he : Real.log (214961125923 / 100000000000) = -Real.log (100000000000 / 214961125923) := by
    rw [show ((214961125923 / 100000000000) : ℝ) = ((100000000000 / 214961125923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13347_neg : (38561637 / 50000000) ≤ -Real.log (250000000000 / 540607581927) ∧
    -Real.log (250000000000 / 540607581927) ≤ (385616371 / 500000000) := by
  have h := checkLog_sound (w := (40607581927 / 1040607581927)) (n := 12)
    (lo := (1952139 / 25000000)) (hi := (78085561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((540607581927 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(540607581927 / 500000000000) = 1/(250000000000 / 540607581927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13347 : Bounds (38561637 / 50000000) (385616371 / 500000000) (Real.log (540607581927 / 250000000000)) := by
  have h := reflection_log_13347_neg
  have he : Real.log (540607581927 / 250000000000) = -Real.log (250000000000 / 540607581927) := by
    rw [show ((540607581927 / 250000000000) : ℝ) = ((250000000000 / 540607581927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13348_neg : (403561403 / 250000000) ≤ -Real.log (500000000000 / 2512048192771) ∧
    -Real.log (500000000000 / 2512048192771) ≤ (322849123 / 200000000) := by
  have h := checkLog_sound (w := (512048192771 / 4512048192771)) (n := 12)
    (lo := (56987813 / 250000000)) (hi := (227951253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2512048192771 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2512048192771 / 2000000000000) = 1/(500000000000 / 2512048192771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13348 : Bounds (403561403 / 250000000) (322849123 / 200000000) (Real.log (2512048192771 / 500000000000)) := by
  have h := reflection_log_13348_neg
  have he : Real.log (2512048192771 / 500000000000) = -Real.log (500000000000 / 2512048192771) := by
    rw [show ((2512048192771 / 500000000000) : ℝ) = ((500000000000 / 2512048192771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13349_neg : (50784993 / 31250000) ≤ -Real.log (125000000000 / 634878419453) ∧
    -Real.log (125000000000 / 634878419453) ≤ (1625119779 / 1000000000) := by
  have h := checkLog_sound (w := (134878419453 / 1134878419453)) (n := 12)
    (lo := (29853177 / 125000000)) (hi := (238825417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((634878419453 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(634878419453 / 500000000000) = 1/(125000000000 / 634878419453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13349 : Bounds (50784993 / 31250000) (1625119779 / 1000000000) (Real.log (634878419453 / 125000000000)) := by
  have h := reflection_log_13349_neg
  have he : Real.log (634878419453 / 125000000000) = -Real.log (125000000000 / 634878419453) := by
    rw [show ((634878419453 / 125000000000) : ℝ) = ((125000000000 / 634878419453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13350_neg : (128803993 / 250000000) ≤ -Real.log (500 / 837) ∧
    -Real.log (500 / 837) ≤ (515215973 / 1000000000) := by
  have h := checkLog_sound (w := (337 / 1337)) (n := 12)
    (lo := (128803993 / 250000000)) (hi := (515215973 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((837 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(837 / 500) = 1/(500 / 837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13350 : Bounds (128803993 / 250000000) (515215973 / 1000000000) (Real.log (837 / 500)) := by
  have h := reflection_log_13350_neg
  have he : Real.log (837 / 500) = -Real.log (500 / 837) := by
    rw [show ((837 / 500) : ℝ) = ((500 / 837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13351_neg : (1120857897 / 1000000000) ≤ -Real.log (163 / 500) ∧
    -Real.log (163 / 500) ≤ (1120857899 / 1000000000) := by
  have h := checkLog_sound (w := (87 / 413)) (n := 12)
    (lo := (427710717 / 1000000000)) (hi := (213855359 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 163) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250 / 163) = 1/(163 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13351 : Bounds (-1120857899 / 1000000000) (-1120857897 / 1000000000) (Real.log (163 / 500)) := by
  have h := reflection_log_13351_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13352_neg : (168443 / 250000000) ≤ -Real.log (500000 / 500337) ∧
    -Real.log (500000 / 500337) ≤ (673773 / 1000000000) := by
  have h := checkLog_sound (w := (337 / 1000337)) (n := 12)
    (lo := (168443 / 250000000)) (hi := (673773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500337 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500337 / 500000) = 1/(500000 / 500337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13352 : Bounds (168443 / 250000000) (673773 / 1000000000) (Real.log (500337 / 500000)) := by
  have h := reflection_log_13352_neg
  have he : Real.log (500337 / 500000) = -Real.log (500000 / 500337) := by
    rw [show ((500337 / 500000) : ℝ) = ((500000 / 500337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13353_neg : (674227 / 1000000000) ≤ -Real.log (499663 / 500000) ∧
    -Real.log (499663 / 500000) ≤ (168557 / 250000000) := by
  have h := checkLog_sound (w := (337 / 999663)) (n := 12)
    (lo := (674227 / 1000000000)) (hi := (168557 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499663) = 1/(499663 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13353 : Bounds (-168557 / 250000000) (-674227 / 1000000000) (Real.log (499663 / 500000)) := by
  have h := reflection_log_13353_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13354_neg : (312600269 / 1000000000) ≤ -Real.log (40000 / 54679) ∧
    -Real.log (40000 / 54679) ≤ (31260027 / 100000000) := by
  have h := checkLog_sound (w := (14679 / 94679)) (n := 12)
    (lo := (312600269 / 1000000000)) (hi := (31260027 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54679 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54679 / 40000) = 1/(40000 / 54679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13354 : Bounds (312600269 / 1000000000) (31260027 / 100000000) (Real.log (54679 / 40000)) := by
  have h := reflection_log_13354_neg
  have he : Real.log (54679 / 40000) = -Real.log (40000 / 54679) := by
    rw [show ((54679 / 40000) : ℝ) = ((40000 / 54679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13355_neg : (457245363 / 1000000000) ≤ -Real.log (25321 / 40000) ∧
    -Real.log (25321 / 40000) ≤ (114311341 / 250000000) := by
  have h := checkLog_sound (w := (14679 / 65321)) (n := 12)
    (lo := (457245363 / 1000000000)) (hi := (114311341 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 25321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 25321) = 1/(25321 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13355 : Bounds (-114311341 / 250000000) (-457245363 / 1000000000) (Real.log (25321 / 40000)) := by
  have h := reflection_log_13355_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13356_neg : (15724403 / 50000000) ≤ -Real.log (500000 / 684779) ∧
    -Real.log (500000 / 684779) ≤ (314488061 / 1000000000) := by
  have h := checkLog_sound (w := (184779 / 1184779)) (n := 12)
    (lo := (15724403 / 50000000)) (hi := (314488061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((684779 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(684779 / 500000) = 1/(500000 / 684779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13356 : Bounds (15724403 / 50000000) (314488061 / 1000000000) (Real.log (684779 / 500000)) := by
  have h := reflection_log_13356_neg
  have he : Real.log (684779 / 500000) = -Real.log (500000 / 684779) := by
    rw [show ((684779 / 500000) : ℝ) = ((500000 / 684779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13357_neg : (230667059 / 500000000) ≤ -Real.log (315221 / 500000) ∧
    -Real.log (315221 / 500000) ≤ (461334119 / 1000000000) := by
  have h := checkLog_sound (w := (184779 / 815221)) (n := 12)
    (lo := (230667059 / 500000000)) (hi := (461334119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 315221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 315221) = 1/(315221 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13357 : Bounds (-461334119 / 1000000000) (-230667059 / 500000000) (Real.log (315221 / 500000)) := by
  have h := reflection_log_13357_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13358_neg : (73423029 / 500000000) ≤ -Real.log (215856721159 / 250000000000) ∧
    -Real.log (215856721159 / 250000000000) ≤ (146846059 / 1000000000) := by
  have h := checkLog_sound (w := (34143278841 / 465856721159)) (n := 12)
    (lo := (73423029 / 500000000)) (hi := (146846059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 215856721159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 215856721159) = 1/(215856721159 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13358 : Bounds (-146846059 / 1000000000) (-73423029 / 500000000) (Real.log (215856721159 / 250000000000)) := by
  have h := reflection_log_13358_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13359_neg : (144645093 / 1000000000) ≤ -Real.log (1384526959 / 1600000000) ∧
    -Real.log (1384526959 / 1600000000) ≤ (72322547 / 500000000) := by
  have h := checkLog_sound (w := (215473041 / 2984526959)) (n := 12)
    (lo := (144645093 / 1000000000)) (hi := (72322547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1384526959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1384526959) = 1/(1384526959 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13359 : Bounds (-72322547 / 500000000) (-144645093 / 1000000000) (Real.log (1384526959 / 1600000000)) := by
  have h := reflection_log_13359_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13360_neg : (769845631 / 1000000000) ≤ -Real.log (250000000000 / 539858220449) ∧
    -Real.log (250000000000 / 539858220449) ≤ (769845633 / 1000000000) := by
  have h := checkLog_sound (w := (39858220449 / 1039858220449)) (n := 12)
    (lo := (76698451 / 1000000000)) (hi := (19174613 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539858220449 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(539858220449 / 500000000000) = 1/(250000000000 / 539858220449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13360 : Bounds (769845631 / 1000000000) (769845633 / 1000000000) (Real.log (539858220449 / 250000000000)) := by
  have h := reflection_log_13360_neg
  have he : Real.log (539858220449 / 250000000000) = -Real.log (250000000000 / 539858220449) := by
    rw [show ((539858220449 / 250000000000) : ℝ) = ((250000000000 / 539858220449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13361_neg : (775822177 / 1000000000) ≤ -Real.log (250000000000 / 543094368713) ∧
    -Real.log (250000000000 / 543094368713) ≤ (775822179 / 1000000000) := by
  have h := checkLog_sound (w := (43094368713 / 1043094368713)) (n := 12)
    (lo := (82674997 / 1000000000)) (hi := (41337499 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((543094368713 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(543094368713 / 500000000000) = 1/(250000000000 / 543094368713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13361 : Bounds (775822177 / 1000000000) (775822179 / 1000000000) (Real.log (543094368713 / 250000000000)) := by
  have h := reflection_log_13361_neg
  have he : Real.log (543094368713 / 250000000000) = -Real.log (250000000000 / 543094368713) := by
    rw [show ((543094368713 / 250000000000) : ℝ) = ((250000000000 / 543094368713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13362_neg : (50784993 / 31250000) ≤ -Real.log (500000000000 / 2539513677811) ∧
    -Real.log (500000000000 / 2539513677811) ≤ (1625119779 / 1000000000) := by
  have h := checkLog_sound (w := (539513677811 / 4539513677811)) (n := 12)
    (lo := (29853177 / 125000000)) (hi := (238825417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2539513677811 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2539513677811 / 2000000000000) = 1/(500000000000 / 2539513677811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13362 : Bounds (50784993 / 31250000) (1625119779 / 1000000000) (Real.log (2539513677811 / 500000000000)) := by
  have h := reflection_log_13362_neg
  have he : Real.log (2539513677811 / 500000000000) = -Real.log (500000000000 / 2539513677811) := by
    rw [show ((2539513677811 / 500000000000) : ℝ) = ((500000000000 / 2539513677811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13363_neg : (409018467 / 250000000) ≤ -Real.log (500000000000 / 2567484662577) ∧
    -Real.log (500000000000 / 2567484662577) ≤ (1636073871 / 1000000000) := by
  have h := checkLog_sound (w := (567484662577 / 4567484662577)) (n := 12)
    (lo := (62444877 / 250000000)) (hi := (249779509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2567484662577 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2567484662577 / 2000000000000) = 1/(500000000000 / 2567484662577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13363 : Bounds (409018467 / 250000000) (1636073871 / 1000000000) (Real.log (2567484662577 / 500000000000)) := by
  have h := reflection_log_13363_neg
  have he : Real.log (2567484662577 / 500000000000) = -Real.log (500000000000 / 2567484662577) := by
    rw [show ((2567484662577 / 500000000000) : ℝ) = ((500000000000 / 2567484662577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13364_neg : (258503241 / 500000000) ≤ -Real.log (1000 / 1677) ∧
    -Real.log (1000 / 1677) ≤ (517006483 / 1000000000) := by
  have h := checkLog_sound (w := (677 / 2677)) (n := 12)
    (lo := (258503241 / 500000000)) (hi := (517006483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1677 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1677 / 1000) = 1/(1000 / 1677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13364 : Bounds (258503241 / 500000000) (517006483 / 1000000000) (Real.log (1677 / 1000)) := by
  have h := reflection_log_13364_neg
  have he : Real.log (1677 / 1000) = -Real.log (1000 / 1677) := by
    rw [show ((1677 / 1000) : ℝ) = ((1000 / 1677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13365_neg : (226020591 / 200000000) ≤ -Real.log (323 / 1000) ∧
    -Real.log (323 / 1000) ≤ (1130102957 / 1000000000) := by
  have h := checkLog_sound (w := (177 / 823)) (n := 12)
    (lo := (17478231 / 40000000)) (hi := (3413717 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 323) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 323) = 1/(323 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13365 : Bounds (-1130102957 / 1000000000) (-226020591 / 200000000) (Real.log (323 / 1000)) := by
  have h := reflection_log_13365_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13366_neg : (67677 / 100000000) ≤ -Real.log (1000000 / 1000677) ∧
    -Real.log (1000000 / 1000677) ≤ (676771 / 1000000000) := by
  have h := checkLog_sound (w := (677 / 2000677)) (n := 12)
    (lo := (67677 / 100000000)) (hi := (676771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000677 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000677 / 1000000) = 1/(1000000 / 1000677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13366 : Bounds (67677 / 100000000) (676771 / 1000000000) (Real.log (1000677 / 1000000)) := by
  have h := reflection_log_13366_neg
  have he : Real.log (1000677 / 1000000) = -Real.log (1000000 / 1000677) := by
    rw [show ((1000677 / 1000000) : ℝ) = ((1000000 / 1000677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13367_neg : (677229 / 1000000000) ≤ -Real.log (999323 / 1000000) ∧
    -Real.log (999323 / 1000000) ≤ (67723 / 100000000) := by
  have h := checkLog_sound (w := (677 / 1999323)) (n := 12)
    (lo := (677229 / 1000000000)) (hi := (67723 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999323) = 1/(999323 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13367 : Bounds (-67723 / 100000000) (-677229 / 1000000000) (Real.log (999323 / 1000000)) := by
  have h := reflection_log_13367_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13368_neg : (62809681 / 200000000) ≤ -Real.log (250000 / 342239) ∧
    -Real.log (250000 / 342239) ≤ (157024203 / 500000000) := by
  have h := checkLog_sound (w := (92239 / 592239)) (n := 12)
    (lo := (62809681 / 200000000)) (hi := (157024203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((342239 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(342239 / 250000) = 1/(250000 / 342239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13368 : Bounds (62809681 / 200000000) (157024203 / 500000000) (Real.log (342239 / 250000)) := by
  have h := reflection_log_13368_neg
  have he : Real.log (342239 / 250000) = -Real.log (250000 / 342239) := by
    rw [show ((342239 / 250000) : ℝ) = ((250000 / 342239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13369_neg : (57547461 / 125000000) ≤ -Real.log (157761 / 250000) ∧
    -Real.log (157761 / 250000) ≤ (460379689 / 1000000000) := by
  have h := checkLog_sound (w := (92239 / 407761)) (n := 12)
    (lo := (57547461 / 125000000)) (hi := (460379689 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 157761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 157761) = 1/(157761 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13369 : Bounds (-460379689 / 1000000000) (-57547461 / 125000000) (Real.log (157761 / 250000)) := by
  have h := reflection_log_13369_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13370_neg : (31593857 / 100000000) ≤ -Real.log (500000 / 685773) ∧
    -Real.log (500000 / 685773) ≤ (315938571 / 1000000000) := by
  have h := checkLog_sound (w := (185773 / 1185773)) (n := 12)
    (lo := (31593857 / 100000000)) (hi := (315938571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((685773 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(685773 / 500000) = 1/(500000 / 685773) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13370 : Bounds (31593857 / 100000000) (315938571 / 1000000000) (Real.log (685773 / 500000)) := by
  have h := reflection_log_13370_neg
  have he : Real.log (685773 / 500000) = -Real.log (500000 / 685773) := by
    rw [show ((685773 / 500000) : ℝ) = ((500000 / 685773) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13371_neg : (464492443 / 1000000000) ≤ -Real.log (314227 / 500000) ∧
    -Real.log (314227 / 500000) ≤ (116123111 / 250000000) := by
  have h := checkLog_sound (w := (185773 / 814227)) (n := 12)
    (lo := (464492443 / 1000000000)) (hi := (116123111 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 314227) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 314227) = 1/(314227 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13371 : Bounds (-116123111 / 250000000) (-464492443 / 1000000000) (Real.log (314227 / 500000)) := by
  have h := reflection_log_13371_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13372_neg : (148553873 / 1000000000) ≤ -Real.log (215488392471 / 250000000000) ∧
    -Real.log (215488392471 / 250000000000) ≤ (74276937 / 500000000) := by
  have h := checkLog_sound (w := (34511607529 / 465488392471)) (n := 12)
    (lo := (148553873 / 1000000000)) (hi := (74276937 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 215488392471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 215488392471) = 1/(215488392471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13372 : Bounds (-74276937 / 500000000) (-148553873 / 1000000000) (Real.log (215488392471 / 250000000000)) := by
  have h := reflection_log_13372_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13373_neg : (73165641 / 500000000) ≤ -Real.log (53991966879 / 62500000000) ∧
    -Real.log (53991966879 / 62500000000) ≤ (146331283 / 1000000000) := by
  have h := checkLog_sound (w := (8508033121 / 116491966879)) (n := 12)
    (lo := (73165641 / 500000000)) (hi := (146331283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 53991966879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 53991966879) = 1/(53991966879 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13373 : Bounds (-146331283 / 1000000000) (-73165641 / 500000000) (Real.log (53991966879 / 62500000000)) := by
  have h := reflection_log_13373_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13374_neg : (774428093 / 1000000000) ≤ -Real.log (500000000000 / 1084675553527) ∧
    -Real.log (500000000000 / 1084675553527) ≤ (154885619 / 200000000) := by
  have h := checkLog_sound (w := (84675553527 / 2084675553527)) (n := 12)
    (lo := (81280913 / 1000000000)) (hi := (40640457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1084675553527 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1084675553527 / 1000000000000) = 1/(500000000000 / 1084675553527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13374 : Bounds (774428093 / 1000000000) (154885619 / 200000000) (Real.log (1084675553527 / 500000000000)) := by
  have h := reflection_log_13374_neg
  have he : Real.log (1084675553527 / 500000000000) = -Real.log (500000000000 / 1084675553527) := by
    rw [show ((1084675553527 / 500000000000) : ℝ) = ((500000000000 / 1084675553527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_13375_neg : (780431013 / 1000000000) ≤ -Real.log (125000000000 / 272801589297) ∧
    -Real.log (125000000000 / 272801589297) ≤ (156086203 / 200000000) := by
  have h := checkLog_sound (w := (22801589297 / 522801589297)) (n := 12)
    (lo := (87283833 / 1000000000)) (hi := (43641917 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272801589297 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(272801589297 / 250000000000) = 1/(125000000000 / 272801589297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13375 : Bounds (780431013 / 1000000000) (156086203 / 200000000) (Real.log (272801589297 / 125000000000)) := by
  have h := reflection_log_13375_neg
  have he : Real.log (272801589297 / 125000000000) = -Real.log (125000000000 / 272801589297) := by
    rw [show ((272801589297 / 125000000000) : ℝ) = ((125000000000 / 272801589297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
