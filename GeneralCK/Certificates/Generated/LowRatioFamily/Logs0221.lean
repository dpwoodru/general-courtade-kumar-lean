import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_14144_neg : (2435572857 / 1000000000) ≤ -Real.log (500000000000 / 5711180124223) ∧
    -Real.log (500000000000 / 5711180124223) ≤ (2435572861 / 1000000000) := by
  have h := checkLog_sound (w := (1711180124223 / 9711180124223)) (n := 12)
    (lo := (356131317 / 1000000000)) (hi := (178065659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5711180124223 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5711180124223 / 4000000000000) = 1/(500000000000 / 5711180124223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14144 : Bounds (2435572857 / 1000000000) (2435572861 / 1000000000) (Real.log (5711180124223 / 500000000000)) := by
  have h := reflection_log_14144_neg
  have he : Real.log (5711180124223 / 500000000000) = -Real.log (500000000000 / 5711180124223) := by
    rw [show ((5711180124223 / 500000000000) : ℝ) = ((500000000000 / 5711180124223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14145_neg : (1228006091 / 500000000) ≤ -Real.log (500000000000 / 5829113924051) ∧
    -Real.log (500000000000 / 5829113924051) ≤ (1228006093 / 500000000) := by
  have h := checkLog_sound (w := (1829113924051 / 9829113924051)) (n := 12)
    (lo := (188285321 / 500000000)) (hi := (376570643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5829113924051 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5829113924051 / 4000000000000) = 1/(500000000000 / 5829113924051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14145 : Bounds (1228006091 / 500000000) (1228006093 / 500000000) (Real.log (5829113924051 / 500000000000)) := by
  have h := reflection_log_14145_neg
  have he : Real.log (5829113924051 / 500000000000) = -Real.log (500000000000 / 5829113924051) := by
    rw [show ((5829113924051 / 500000000000) : ℝ) = ((500000000000 / 5829113924051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14146_neg : (612479277 / 1000000000) ≤ -Real.log (200 / 369) ∧
    -Real.log (200 / 369) ≤ (306239639 / 500000000) := by
  have h := checkLog_sound (w := (169 / 569)) (n := 12)
    (lo := (612479277 / 1000000000)) (hi := (306239639 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((369 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(369 / 200) = 1/(200 / 369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14146 : Bounds (612479277 / 1000000000) (306239639 / 500000000) (Real.log (369 / 200)) := by
  have h := reflection_log_14146_neg
  have he : Real.log (369 / 200) = -Real.log (200 / 369) := by
    rw [show ((369 / 200) : ℝ) = ((200 / 369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14147_neg : (23304127 / 12500000) ≤ -Real.log (31 / 200) ∧
    -Real.log (31 / 200) ≤ (1864330163 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 81)) (n := 12)
    (lo := (2390179 / 5000000)) (hi := (478035801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50 / 31) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50 / 31) = 1/(31 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14147 : Bounds (-1864330163 / 1000000000) (-23304127 / 12500000) (Real.log (31 / 200)) := by
  have h := reflection_log_14147_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14148_neg : (844643 / 1000000000) ≤ -Real.log (200000 / 200169) ∧
    -Real.log (200000 / 200169) ≤ (211161 / 250000000) := by
  have h := checkLog_sound (w := (169 / 400169)) (n := 12)
    (lo := (844643 / 1000000000)) (hi := (211161 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200169 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200169 / 200000) = 1/(200000 / 200169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14148 : Bounds (844643 / 1000000000) (211161 / 250000000) (Real.log (200169 / 200000)) := by
  have h := reflection_log_14148_neg
  have he : Real.log (200169 / 200000) = -Real.log (200000 / 200169) := by
    rw [show ((200169 / 200000) : ℝ) = ((200000 / 200169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14149_neg : (845357 / 1000000000) ≤ -Real.log (199831 / 200000) ∧
    -Real.log (199831 / 200000) ≤ (422679 / 500000000) := by
  have h := checkLog_sound (w := (169 / 399831)) (n := 12)
    (lo := (845357 / 1000000000)) (hi := (422679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199831) = 1/(199831 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14149 : Bounds (-422679 / 500000000) (-845357 / 1000000000) (Real.log (199831 / 200000)) := by
  have h := reflection_log_14149_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14150_neg : (399973389 / 1000000000) ≤ -Real.log (200000 / 298357) ∧
    -Real.log (200000 / 298357) ≤ (39997339 / 100000000) := by
  have h := checkLog_sound (w := (98357 / 498357)) (n := 12)
    (lo := (399973389 / 1000000000)) (hi := (39997339 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298357 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298357 / 200000) = 1/(200000 / 298357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14150 : Bounds (399973389 / 1000000000) (39997339 / 100000000) (Real.log (298357 / 200000)) := by
  have h := reflection_log_14150_neg
  have he : Real.log (298357 / 200000) = -Real.log (200000 / 298357) := by
    rw [show ((298357 / 200000) : ℝ) = ((200000 / 298357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14151_neg : (169212673 / 250000000) ≤ -Real.log (101643 / 200000) ∧
    -Real.log (101643 / 200000) ≤ (676850693 / 1000000000) := by
  have h := checkLog_sound (w := (98357 / 301643)) (n := 12)
    (lo := (169212673 / 250000000)) (hi := (676850693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 101643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 101643) = 1/(101643 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14151 : Bounds (-676850693 / 1000000000) (-169212673 / 250000000) (Real.log (101643 / 200000)) := by
  have h := reflection_log_14151_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14152_neg : (5026009 / 12500000) ≤ -Real.log (250000 / 373733) ∧
    -Real.log (250000 / 373733) ≤ (402080721 / 1000000000) := by
  have h := checkLog_sound (w := (123733 / 623733)) (n := 12)
    (lo := (5026009 / 12500000)) (hi := (402080721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((373733 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(373733 / 250000) = 1/(250000 / 373733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14152 : Bounds (5026009 / 12500000) (402080721 / 1000000000) (Real.log (373733 / 250000)) := by
  have h := reflection_log_14152_neg
  have he : Real.log (373733 / 250000) = -Real.log (250000 / 373733) := by
    rw [show ((373733 / 250000) : ℝ) = ((250000 / 373733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14153_neg : (136612441 / 200000000) ≤ -Real.log (126267 / 250000) ∧
    -Real.log (126267 / 250000) ≤ (341531103 / 500000000) := by
  have h := checkLog_sound (w := (123733 / 376267)) (n := 12)
    (lo := (136612441 / 200000000)) (hi := (341531103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 126267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 126267) = 1/(126267 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14153 : Bounds (-341531103 / 500000000) (-136612441 / 200000000) (Real.log (126267 / 250000)) := by
  have h := reflection_log_14153_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14154_neg : (70245371 / 250000000) ≤ -Real.log (47190144711 / 62500000000) ∧
    -Real.log (47190144711 / 62500000000) ≤ (56196297 / 200000000) := by
  have h := checkLog_sound (w := (15309855289 / 109690144711)) (n := 12)
    (lo := (70245371 / 250000000)) (hi := (56196297 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 47190144711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 47190144711) = 1/(47190144711 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14154 : Bounds (-56196297 / 200000000) (-70245371 / 250000000) (Real.log (47190144711 / 62500000000)) := by
  have h := reflection_log_14154_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14155_neg : (276877303 / 1000000000) ≤ -Real.log (30325900551 / 40000000000) ∧
    -Real.log (30325900551 / 40000000000) ≤ (34609663 / 125000000) := by
  have h := checkLog_sound (w := (9674099449 / 70325900551)) (n := 12)
    (lo := (276877303 / 1000000000)) (hi := (34609663 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 30325900551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 30325900551) = 1/(30325900551 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14155 : Bounds (-34609663 / 125000000) (-276877303 / 1000000000) (Real.log (30325900551 / 40000000000)) := by
  have h := reflection_log_14155_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14156_neg : (1076824081 / 1000000000) ≤ -Real.log (100000000000 / 293534232559) ∧
    -Real.log (100000000000 / 293534232559) ≤ (1076824083 / 1000000000) := by
  have h := checkLog_sound (w := (93534232559 / 493534232559)) (n := 12)
    (lo := (383676901 / 1000000000)) (hi := (191838451 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293534232559 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(293534232559 / 200000000000) = 1/(100000000000 / 293534232559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14156 : Bounds (1076824081 / 1000000000) (1076824083 / 1000000000) (Real.log (293534232559 / 100000000000)) := by
  have h := reflection_log_14156_neg
  have he : Real.log (293534232559 / 100000000000) = -Real.log (100000000000 / 293534232559) := by
    rw [show ((293534232559 / 100000000000) : ℝ) = ((100000000000 / 293534232559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14157_neg : (43405717 / 40000000) ≤ -Real.log (62500000000 / 184991426897) ∧
    -Real.log (62500000000 / 184991426897) ≤ (1085142927 / 1000000000) := by
  have h := checkLog_sound (w := (59991426897 / 309991426897)) (n := 12)
    (lo := (78399149 / 200000000)) (hi := (195997873 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((184991426897 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(184991426897 / 125000000000) = 1/(62500000000 / 184991426897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14157 : Bounds (43405717 / 40000000) (1085142927 / 1000000000) (Real.log (184991426897 / 62500000000)) := by
  have h := reflection_log_14157_neg
  have he : Real.log (184991426897 / 62500000000) = -Real.log (62500000000 / 184991426897) := by
    rw [show ((184991426897 / 62500000000) : ℝ) = ((62500000000 / 184991426897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14158_neg : (1228006091 / 500000000) ≤ -Real.log (10000000000 / 116582278481) ∧
    -Real.log (10000000000 / 116582278481) ≤ (1228006093 / 500000000) := by
  have h := checkLog_sound (w := (36582278481 / 196582278481)) (n := 12)
    (lo := (188285321 / 500000000)) (hi := (376570643 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((116582278481 / 80000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(116582278481 / 80000000000) = 1/(10000000000 / 116582278481) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14158 : Bounds (1228006091 / 500000000) (1228006093 / 500000000) (Real.log (116582278481 / 10000000000)) := by
  have h := reflection_log_14158_neg
  have he : Real.log (116582278481 / 10000000000) = -Real.log (10000000000 / 116582278481) := by
    rw [show ((116582278481 / 10000000000) : ℝ) = ((10000000000 / 116582278481) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14159_neg : (2476809437 / 1000000000) ≤ -Real.log (250000000000 / 2975806451613) ∧
    -Real.log (250000000000 / 2975806451613) ≤ (2476809441 / 1000000000) := by
  have h := checkLog_sound (w := (975806451613 / 4975806451613)) (n := 12)
    (lo := (397367897 / 1000000000)) (hi := (198683949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2975806451613 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2975806451613 / 2000000000000) = 1/(250000000000 / 2975806451613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14159 : Bounds (2476809437 / 1000000000) (2476809441 / 1000000000) (Real.log (2975806451613 / 250000000000)) := by
  have h := reflection_log_14159_neg
  have he : Real.log (2975806451613 / 250000000000) = -Real.log (250000000000 / 2975806451613) := by
    rw [show ((2975806451613 / 250000000000) : ℝ) = ((250000000000 / 2975806451613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14160_neg : (614103973 / 1000000000) ≤ -Real.log (125 / 231) ∧
    -Real.log (125 / 231) ≤ (307051987 / 500000000) := by
  have h := checkLog_sound (w := (53 / 178)) (n := 12)
    (lo := (614103973 / 1000000000)) (hi := (307051987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((231 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(231 / 125) = 1/(125 / 231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14160 : Bounds (614103973 / 1000000000) (307051987 / 500000000) (Real.log (231 / 125)) := by
  have h := reflection_log_14160_neg
  have he : Real.log (231 / 125) = -Real.log (125 / 231) := by
    rw [show ((231 / 125) : ℝ) = ((125 / 231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14161_neg : (1883874757 / 1000000000) ≤ -Real.log (19 / 125) ∧
    -Real.log (19 / 125) ≤ (47096869 / 25000000) := by
  have h := checkLog_sound (w := (49 / 201)) (n := 12)
    (lo := (497580397 / 1000000000)) (hi := (248790199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 76) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 76) = 1/(19 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14161 : Bounds (-47096869 / 25000000) (-1883874757 / 1000000000) (Real.log (19 / 125)) := by
  have h := reflection_log_14161_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14162_neg : (21191 / 25000000) ≤ -Real.log (62500 / 62553) ∧
    -Real.log (62500 / 62553) ≤ (847641 / 1000000000) := by
  have h := checkLog_sound (w := (53 / 125053)) (n := 12)
    (lo := (21191 / 25000000)) (hi := (847641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62553 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62553 / 62500) = 1/(62500 / 62553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14162 : Bounds (21191 / 25000000) (847641 / 1000000000) (Real.log (62553 / 62500)) := by
  have h := reflection_log_14162_neg
  have he : Real.log (62553 / 62500) = -Real.log (62500 / 62553) := by
    rw [show ((62553 / 62500) : ℝ) = ((62500 / 62553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14163_neg : (848359 / 1000000000) ≤ -Real.log (62447 / 62500) ∧
    -Real.log (62447 / 62500) ≤ (21209 / 25000000) := by
  have h := checkLog_sound (w := (53 / 124947)) (n := 12)
    (lo := (848359 / 1000000000)) (hi := (21209 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62447) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62447) = 1/(62447 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14163 : Bounds (-21209 / 25000000) (-848359 / 1000000000) (Real.log (62447 / 62500)) := by
  have h := reflection_log_14163_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14164_neg : (401631101 / 1000000000) ≤ -Real.log (50000 / 74713) ∧
    -Real.log (50000 / 74713) ≤ (200815551 / 500000000) := by
  have h := checkLog_sound (w := (24713 / 124713)) (n := 12)
    (lo := (401631101 / 1000000000)) (hi := (200815551 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74713 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(74713 / 50000) = 1/(50000 / 74713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14164 : Bounds (401631101 / 1000000000) (200815551 / 500000000) (Real.log (74713 / 50000)) := by
  have h := reflection_log_14164_neg
  have he : Real.log (74713 / 50000) = -Real.log (50000 / 74713) := by
    rw [show ((74713 / 50000) : ℝ) = ((50000 / 74713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14165_neg : (27269303 / 40000000) ≤ -Real.log (25287 / 50000) ∧
    -Real.log (25287 / 50000) ≤ (21304143 / 31250000) := by
  have h := checkLog_sound (w := (24713 / 75287)) (n := 12)
    (lo := (27269303 / 40000000)) (hi := (21304143 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 25287) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 25287) = 1/(25287 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14165 : Bounds (-21304143 / 31250000) (-27269303 / 40000000) (Real.log (25287 / 50000)) := by
  have h := reflection_log_14165_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14166_neg : (80748859 / 200000000) ≤ -Real.log (1000000 / 1497421) ∧
    -Real.log (1000000 / 1497421) ≤ (50468037 / 125000000) := by
  have h := checkLog_sound (w := (497421 / 2497421)) (n := 12)
    (lo := (80748859 / 200000000)) (hi := (50468037 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1497421 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1497421 / 1000000) = 1/(1000000 / 1497421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14166 : Bounds (80748859 / 200000000) (50468037 / 125000000) (Real.log (1497421 / 1000000)) := by
  have h := reflection_log_14166_neg
  have he : Real.log (1497421 / 1000000) = -Real.log (1000000 / 1497421) := by
    rw [show ((1497421 / 1000000) : ℝ) = ((1000000 / 1497421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14167_neg : (688002437 / 1000000000) ≤ -Real.log (502579 / 1000000) ∧
    -Real.log (502579 / 1000000) ≤ (344001219 / 500000000) := by
  have h := checkLog_sound (w := (497421 / 1502579)) (n := 12)
    (lo := (688002437 / 1000000000)) (hi := (344001219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 502579) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 502579) = 1/(502579 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14167 : Bounds (-344001219 / 500000000) (-688002437 / 1000000000) (Real.log (502579 / 1000000)) := by
  have h := reflection_log_14167_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14168_neg : (142129071 / 500000000) ≤ -Real.log (752572348759 / 1000000000000) ∧
    -Real.log (752572348759 / 1000000000000) ≤ (284258143 / 1000000000) := by
  have h := checkLog_sound (w := (247427651241 / 1752572348759)) (n := 12)
    (lo := (142129071 / 500000000)) (hi := (284258143 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 752572348759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 752572348759) = 1/(752572348759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14168 : Bounds (-284258143 / 1000000000) (-142129071 / 500000000) (Real.log (752572348759 / 1000000000000)) := by
  have h := reflection_log_14168_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14169_neg : (140050737 / 500000000) ≤ -Real.log (1889267631 / 2500000000) ∧
    -Real.log (1889267631 / 2500000000) ≤ (11204059 / 40000000) := by
  have h := checkLog_sound (w := (610732369 / 4389267631)) (n := 12)
    (lo := (140050737 / 500000000)) (hi := (11204059 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 1889267631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 1889267631) = 1/(1889267631 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14169 : Bounds (-11204059 / 40000000) (-140050737 / 500000000) (Real.log (1889267631 / 2500000000)) := by
  have h := reflection_log_14169_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14170_neg : (270840919 / 250000000) ≤ -Real.log (100000000000 / 295460117847) ∧
    -Real.log (100000000000 / 295460117847) ≤ (541681839 / 500000000) := by
  have h := checkLog_sound (w := (95460117847 / 495460117847)) (n := 12)
    (lo := (24388531 / 62500000)) (hi := (390216497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295460117847 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(295460117847 / 200000000000) = 1/(100000000000 / 295460117847) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14170 : Bounds (270840919 / 250000000) (541681839 / 500000000) (Real.log (295460117847 / 100000000000)) := by
  have h := reflection_log_14170_neg
  have he : Real.log (295460117847 / 100000000000) = -Real.log (100000000000 / 295460117847) := by
    rw [show ((295460117847 / 100000000000) : ℝ) = ((100000000000 / 295460117847) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14171_neg : (1091746731 / 1000000000) ≤ -Real.log (6250000000 / 18621711711) ∧
    -Real.log (6250000000 / 18621711711) ≤ (1091746733 / 1000000000) := by
  have h := checkLog_sound (w := (6121711711 / 31121711711)) (n := 12)
    (lo := (398599551 / 1000000000)) (hi := (3114059 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18621711711 / 12500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(18621711711 / 12500000000) = 1/(6250000000 / 18621711711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14171 : Bounds (1091746731 / 1000000000) (1091746733 / 1000000000) (Real.log (18621711711 / 6250000000)) := by
  have h := reflection_log_14171_neg
  have he : Real.log (18621711711 / 6250000000) = -Real.log (6250000000 / 18621711711) := by
    rw [show ((18621711711 / 6250000000) : ℝ) = ((6250000000 / 18621711711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14172_neg : (2476809437 / 1000000000) ≤ -Real.log (20000000000 / 238064516129) ∧
    -Real.log (20000000000 / 238064516129) ≤ (2476809441 / 1000000000) := by
  have h := checkLog_sound (w := (78064516129 / 398064516129)) (n := 12)
    (lo := (397367897 / 1000000000)) (hi := (198683949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((238064516129 / 160000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(238064516129 / 160000000000) = 1/(20000000000 / 238064516129) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14172 : Bounds (2476809437 / 1000000000) (2476809441 / 1000000000) (Real.log (238064516129 / 20000000000)) := by
  have h := reflection_log_14172_neg
  have he : Real.log (238064516129 / 20000000000) = -Real.log (20000000000 / 238064516129) := by
    rw [show ((238064516129 / 20000000000) : ℝ) = ((20000000000 / 238064516129) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14173_neg : (2497978729 / 1000000000) ≤ -Real.log (250000000000 / 3039473684211) ∧
    -Real.log (250000000000 / 3039473684211) ≤ (2497978733 / 1000000000) := by
  have h := checkLog_sound (w := (1039473684211 / 5039473684211)) (n := 12)
    (lo := (418537189 / 1000000000)) (hi := (41853719 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3039473684211 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3039473684211 / 2000000000000) = 1/(250000000000 / 3039473684211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14173 : Bounds (2497978729 / 1000000000) (2497978733 / 1000000000) (Real.log (3039473684211 / 250000000000)) := by
  have h := reflection_log_14173_neg
  have he : Real.log (3039473684211 / 250000000000) = -Real.log (250000000000 / 3039473684211) := by
    rw [show ((3039473684211 / 250000000000) : ℝ) = ((250000000000 / 3039473684211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14174_neg : (615726033 / 1000000000) ≤ -Real.log (1000 / 1851) ∧
    -Real.log (1000 / 1851) ≤ (307863017 / 500000000) := by
  have h := checkLog_sound (w := (851 / 2851)) (n := 12)
    (lo := (615726033 / 1000000000)) (hi := (307863017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1851 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1851 / 1000) = 1/(1000 / 1851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14174 : Bounds (615726033 / 1000000000) (307863017 / 500000000) (Real.log (1851 / 1000)) := by
  have h := reflection_log_14174_neg
  have he : Real.log (1851 / 1000) = -Real.log (1000 / 1851) := by
    rw [show ((1851 / 1000) : ℝ) = ((1000 / 1851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14175_neg : (1903808971 / 1000000000) ≤ -Real.log (149 / 1000) ∧
    -Real.log (149 / 1000) ≤ (951904487 / 500000000) := by
  have h := checkLog_sound (w := (101 / 399)) (n := 12)
    (lo := (517514611 / 1000000000)) (hi := (129378653 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 149) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 149) = 1/(149 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14175 : Bounds (-951904487 / 500000000) (-1903808971 / 1000000000) (Real.log (149 / 1000)) := by
  have h := reflection_log_14175_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14176_neg : (425319 / 500000000) ≤ -Real.log (1000000 / 1000851) ∧
    -Real.log (1000000 / 1000851) ≤ (850639 / 1000000000) := by
  have h := checkLog_sound (w := (851 / 2000851)) (n := 12)
    (lo := (425319 / 500000000)) (hi := (850639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000851 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000851 / 1000000) = 1/(1000000 / 1000851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14176 : Bounds (425319 / 500000000) (850639 / 1000000000) (Real.log (1000851 / 1000000)) := by
  have h := reflection_log_14176_neg
  have he : Real.log (1000851 / 1000000) = -Real.log (1000000 / 1000851) := by
    rw [show ((1000851 / 1000000) : ℝ) = ((1000000 / 1000851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14177_neg : (425681 / 500000000) ≤ -Real.log (999149 / 1000000) ∧
    -Real.log (999149 / 1000000) ≤ (851363 / 1000000000) := by
  have h := checkLog_sound (w := (851 / 1999149)) (n := 12)
    (lo := (425681 / 500000000)) (hi := (851363 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999149) = 1/(999149 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14177 : Bounds (-851363 / 1000000000) (-425681 / 500000000) (Real.log (999149 / 1000000)) := by
  have h := reflection_log_14177_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14178_neg : (201647377 / 500000000) ≤ -Real.log (250000 / 374187) ∧
    -Real.log (250000 / 374187) ≤ (80658951 / 200000000) := by
  have h := checkLog_sound (w := (124187 / 624187)) (n := 12)
    (lo := (201647377 / 500000000)) (hi := (80658951 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((374187 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(374187 / 250000) = 1/(250000 / 374187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14178 : Bounds (201647377 / 500000000) (80658951 / 200000000) (Real.log (374187 / 250000)) := by
  have h := reflection_log_14178_neg
  have he : Real.log (374187 / 250000) = -Real.log (250000 / 374187) := by
    rw [show ((374187 / 250000) : ℝ) = ((250000 / 374187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14179_neg : (8583303 / 12500000) ≤ -Real.log (125813 / 250000) ∧
    -Real.log (125813 / 250000) ≤ (686664241 / 1000000000) := by
  have h := checkLog_sound (w := (124187 / 375813)) (n := 12)
    (lo := (8583303 / 12500000)) (hi := (686664241 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 125813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 125813) = 1/(125813 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14179 : Bounds (-686664241 / 1000000000) (-8583303 / 12500000) (Real.log (125813 / 250000)) := by
  have h := reflection_log_14179_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14180_neg : (405413773 / 1000000000) ≤ -Real.log (1000000 / 1499923) ∧
    -Real.log (1000000 / 1499923) ≤ (202706887 / 500000000) := by
  have h := checkLog_sound (w := (499923 / 2499923)) (n := 12)
    (lo := (405413773 / 1000000000)) (hi := (202706887 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1499923 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1499923 / 1000000) = 1/(1000000 / 1499923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14180 : Bounds (405413773 / 1000000000) (202706887 / 500000000) (Real.log (1499923 / 1000000)) := by
  have h := reflection_log_14180_neg
  have he : Real.log (1499923 / 1000000) = -Real.log (1000000 / 1499923) := by
    rw [show ((1499923 / 1000000) : ℝ) = ((1000000 / 1499923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14181_neg : (86624149 / 125000000) ≤ -Real.log (500077 / 1000000) ∧
    -Real.log (500077 / 1000000) ≤ (692993193 / 1000000000) := by
  have h := checkLog_sound (w := (499923 / 1500077)) (n := 12)
    (lo := (86624149 / 125000000)) (hi := (692993193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 500077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 500077) = 1/(500077 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14181 : Bounds (-692993193 / 1000000000) (-86624149 / 125000000) (Real.log (500077 / 1000000)) := by
  have h := reflection_log_14181_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14182_neg : (143789709 / 500000000) ≤ -Real.log (750076994071 / 1000000000000) ∧
    -Real.log (750076994071 / 1000000000000) ≤ (287579419 / 1000000000) := by
  have h := checkLog_sound (w := (249923005929 / 1750076994071)) (n := 12)
    (lo := (143789709 / 500000000)) (hi := (287579419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 750076994071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 750076994071) = 1/(750076994071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14182 : Bounds (-287579419 / 1000000000) (-143789709 / 500000000) (Real.log (750076994071 / 1000000000000)) := by
  have h := reflection_log_14182_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14183_neg : (56673897 / 200000000) ≤ -Real.log (47077589031 / 62500000000) ∧
    -Real.log (47077589031 / 62500000000) ≤ (141684743 / 500000000) := by
  have h := checkLog_sound (w := (15422410969 / 109577589031)) (n := 12)
    (lo := (56673897 / 200000000)) (hi := (141684743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 47077589031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 47077589031) = 1/(47077589031 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14183 : Bounds (-141684743 / 500000000) (-56673897 / 200000000) (Real.log (47077589031 / 62500000000)) := by
  have h := reflection_log_14183_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14184_neg : (544979497 / 500000000) ≤ -Real.log (500000000000 / 1487076057323) ∧
    -Real.log (500000000000 / 1487076057323) ≤ (272489749 / 250000000) := by
  have h := checkLog_sound (w := (487076057323 / 2487076057323)) (n := 12)
    (lo := (198405907 / 500000000)) (hi := (79362363 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1487076057323 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1487076057323 / 1000000000000) = 1/(500000000000 / 1487076057323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14184 : Bounds (544979497 / 500000000) (272489749 / 250000000) (Real.log (1487076057323 / 500000000000)) := by
  have h := reflection_log_14184_neg
  have he : Real.log (1487076057323 / 500000000000) = -Real.log (500000000000 / 1487076057323) := by
    rw [show ((1487076057323 / 500000000000) : ℝ) = ((500000000000 / 1487076057323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14185_neg : (219681393 / 200000000) ≤ -Real.log (20000000000 / 59987681897) ∧
    -Real.log (20000000000 / 59987681897) ≤ (1098406967 / 1000000000) := by
  have h := checkLog_sound (w := (19987681897 / 99987681897)) (n := 12)
    (lo := (81051957 / 200000000)) (hi := (202629893 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59987681897 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(59987681897 / 40000000000) = 1/(20000000000 / 59987681897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14185 : Bounds (219681393 / 200000000) (1098406967 / 1000000000) (Real.log (59987681897 / 20000000000)) := by
  have h := reflection_log_14185_neg
  have he : Real.log (59987681897 / 20000000000) = -Real.log (20000000000 / 59987681897) := by
    rw [show ((59987681897 / 20000000000) : ℝ) = ((20000000000 / 59987681897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14186_neg : (2497978729 / 1000000000) ≤ -Real.log (500000000000 / 6078947368421) ∧
    -Real.log (500000000000 / 6078947368421) ≤ (2497978733 / 1000000000) := by
  have h := checkLog_sound (w := (2078947368421 / 10078947368421)) (n := 12)
    (lo := (418537189 / 1000000000)) (hi := (41853719 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6078947368421 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6078947368421 / 4000000000000) = 1/(500000000000 / 6078947368421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14186 : Bounds (2497978729 / 1000000000) (2497978733 / 1000000000) (Real.log (6078947368421 / 500000000000)) := by
  have h := reflection_log_14186_neg
  have he : Real.log (6078947368421 / 500000000000) = -Real.log (500000000000 / 6078947368421) := by
    rw [show ((6078947368421 / 500000000000) : ℝ) = ((500000000000 / 6078947368421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14187_neg : (629883751 / 250000000) ≤ -Real.log (250000000000 / 3105704697987) ∧
    -Real.log (250000000000 / 3105704697987) ≤ (78735469 / 31250000) := by
  have h := checkLog_sound (w := (1105704697987 / 5105704697987)) (n := 12)
    (lo := (55011683 / 125000000)) (hi := (88018693 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3105704697987 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3105704697987 / 2000000000000) = 1/(250000000000 / 3105704697987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14187 : Bounds (629883751 / 250000000) (78735469 / 31250000) (Real.log (3105704697987 / 250000000000)) := by
  have h := reflection_log_14187_neg
  have he : Real.log (3105704697987 / 250000000000) = -Real.log (250000000000 / 3105704697987) := by
    rw [show ((3105704697987 / 250000000000) : ℝ) = ((250000000000 / 3105704697987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14188_neg : (617345467 / 1000000000) ≤ -Real.log (500 / 927) ∧
    -Real.log (500 / 927) ≤ (154336367 / 250000000) := by
  have h := checkLog_sound (w := (427 / 1427)) (n := 12)
    (lo := (617345467 / 1000000000)) (hi := (154336367 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((927 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(927 / 500) = 1/(500 / 927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14188 : Bounds (617345467 / 1000000000) (154336367 / 250000000) (Real.log (927 / 500)) := by
  have h := reflection_log_14188_neg
  have he : Real.log (927 / 500) = -Real.log (500 / 927) := by
    rw [show ((927 / 500) : ℝ) = ((500 / 927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14189_neg : (120259291 / 62500000) ≤ -Real.log (73 / 500) ∧
    -Real.log (73 / 500) ≤ (1924148659 / 1000000000) := by
  have h := checkLog_sound (w := (26 / 99)) (n := 12)
    (lo := (67231787 / 125000000)) (hi := (537854297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 73) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125 / 73) = 1/(73 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14189 : Bounds (-1924148659 / 1000000000) (-120259291 / 62500000) (Real.log (73 / 500)) := by
  have h := reflection_log_14189_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14190_neg : (170727 / 200000000) ≤ -Real.log (500000 / 500427) ∧
    -Real.log (500000 / 500427) ≤ (213409 / 250000000) := by
  have h := checkLog_sound (w := (427 / 1000427)) (n := 12)
    (lo := (170727 / 200000000)) (hi := (213409 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500427 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500427 / 500000) = 1/(500000 / 500427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14190 : Bounds (170727 / 200000000) (213409 / 250000000) (Real.log (500427 / 500000)) := by
  have h := reflection_log_14190_neg
  have he : Real.log (500427 / 500000) = -Real.log (500000 / 500427) := by
    rw [show ((500427 / 500000) : ℝ) = ((500000 / 500427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14191_neg : (213591 / 250000000) ≤ -Real.log (499573 / 500000) ∧
    -Real.log (499573 / 500000) ≤ (170873 / 200000000) := by
  have h := checkLog_sound (w := (427 / 999573)) (n := 12)
    (lo := (213591 / 250000000)) (hi := (170873 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499573) = 1/(499573 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14191 : Bounds (-170873 / 200000000) (-213591 / 250000000) (Real.log (499573 / 500000)) := by
  have h := reflection_log_14191_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14192_neg : (404964983 / 1000000000) ≤ -Real.log (4000 / 5997) ∧
    -Real.log (4000 / 5997) ≤ (50620623 / 125000000) := by
  have h := checkLog_sound (w := (1997 / 9997)) (n := 12)
    (lo := (404964983 / 1000000000)) (hi := (50620623 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5997 / 4000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5997 / 4000) = 1/(4000 / 5997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14192 : Bounds (404964983 / 1000000000) (50620623 / 125000000) (Real.log (5997 / 4000)) := by
  have h := reflection_log_14192_neg
  have he : Real.log (5997 / 4000) = -Real.log (4000 / 5997) := by
    rw [show ((5997 / 4000) : ℝ) = ((4000 / 5997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14193_neg : (43228019 / 62500000) ≤ -Real.log (2003 / 4000) ∧
    -Real.log (2003 / 4000) ≤ (138329661 / 200000000) := by
  have h := checkLog_sound (w := (1997 / 6003)) (n := 12)
    (lo := (43228019 / 62500000)) (hi := (138329661 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000 / 2003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000 / 2003) = 1/(2003 / 4000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14193 : Bounds (-138329661 / 200000000) (-43228019 / 62500000) (Real.log (2003 / 4000)) := by
  have h := reflection_log_14193_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14194_neg : (407089787 / 1000000000) ≤ -Real.log (1000000 / 1502439) ∧
    -Real.log (1000000 / 1502439) ≤ (101772447 / 250000000) := by
  have h := checkLog_sound (w := (502439 / 2502439)) (n := 12)
    (lo := (407089787 / 1000000000)) (hi := (101772447 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1502439 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1502439 / 1000000) = 1/(1000000 / 1502439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14194 : Bounds (407089787 / 1000000000) (101772447 / 250000000) (Real.log (1502439 / 1000000)) := by
  have h := reflection_log_14194_neg
  have he : Real.log (1502439 / 1000000) = -Real.log (1000000 / 1502439) := by
    rw [show ((1502439 / 1000000) : ℝ) = ((1000000 / 1502439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14195_neg : (174509279 / 250000000) ≤ -Real.log (497561 / 1000000) ∧
    -Real.log (497561 / 1000000) ≤ (349018559 / 500000000) := by
  have h := checkLog_sound (w := (2439 / 997561)) (n := 12)
    (lo := (305621 / 62500000)) (hi := (4889937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 497561) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 497561) = 1/(497561 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14195 : Bounds (-349018559 / 500000000) (-174509279 / 250000000) (Real.log (497561 / 1000000)) := by
  have h := reflection_log_14195_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14196_neg : (290947329 / 1000000000) ≤ -Real.log (747555051279 / 1000000000000) ∧
    -Real.log (747555051279 / 1000000000000) ≤ (29094733 / 100000000) := by
  have h := checkLog_sound (w := (252444948721 / 1747555051279)) (n := 12)
    (lo := (290947329 / 1000000000)) (hi := (29094733 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 747555051279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 747555051279) = 1/(747555051279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14196 : Bounds (-29094733 / 100000000) (-290947329 / 1000000000) (Real.log (747555051279 / 1000000000000)) := by
  have h := reflection_log_14196_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14197_neg : (286683321 / 1000000000) ≤ -Real.log (12011991 / 16000000) ∧
    -Real.log (12011991 / 16000000) ≤ (143341661 / 500000000) := by
  have h := checkLog_sound (w := (3988009 / 28011991)) (n := 12)
    (lo := (286683321 / 1000000000)) (hi := (143341661 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16000000 / 12011991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16000000 / 12011991) = 1/(12011991 / 16000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14197 : Bounds (-143341661 / 500000000) (-286683321 / 1000000000) (Real.log (12011991 / 16000000)) := by
  have h := reflection_log_14197_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14198_neg : (548306643 / 500000000) ≤ -Real.log (25000000000 / 74850224663) ∧
    -Real.log (25000000000 / 74850224663) ≤ (137076661 / 125000000) := by
  have h := checkLog_sound (w := (24850224663 / 124850224663)) (n := 12)
    (lo := (201733053 / 500000000)) (hi := (403466107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((74850224663 / 50000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(74850224663 / 50000000000) = 1/(25000000000 / 74850224663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14198 : Bounds (548306643 / 500000000) (137076661 / 125000000) (Real.log (74850224663 / 25000000000)) := by
  have h := reflection_log_14198_neg
  have he : Real.log (74850224663 / 25000000000) = -Real.log (25000000000 / 74850224663) := by
    rw [show ((74850224663 / 25000000000) : ℝ) = ((25000000000 / 74850224663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14199_neg : (1105126903 / 1000000000) ≤ -Real.log (500000000000 / 1509803823049) ∧
    -Real.log (500000000000 / 1509803823049) ≤ (221025381 / 200000000) := by
  have h := checkLog_sound (w := (509803823049 / 2509803823049)) (n := 12)
    (lo := (411979723 / 1000000000)) (hi := (102994931 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1509803823049 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1509803823049 / 1000000000000) = 1/(500000000000 / 1509803823049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14199 : Bounds (1105126903 / 1000000000) (221025381 / 200000000) (Real.log (1509803823049 / 500000000000)) := by
  have h := reflection_log_14199_neg
  have he : Real.log (1509803823049 / 500000000000) = -Real.log (500000000000 / 1509803823049) := by
    rw [show ((1509803823049 / 500000000000) : ℝ) = ((500000000000 / 1509803823049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14200_neg : (629883751 / 250000000) ≤ -Real.log (500000000000 / 6211409395973) ∧
    -Real.log (500000000000 / 6211409395973) ≤ (78735469 / 31250000) := by
  have h := checkLog_sound (w := (2211409395973 / 10211409395973)) (n := 12)
    (lo := (55011683 / 125000000)) (hi := (88018693 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6211409395973 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(6211409395973 / 4000000000000) = 1/(500000000000 / 6211409395973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14200 : Bounds (629883751 / 250000000) (78735469 / 31250000) (Real.log (6211409395973 / 500000000000)) := by
  have h := reflection_log_14200_neg
  have he : Real.log (6211409395973 / 500000000000) = -Real.log (500000000000 / 6211409395973) := by
    rw [show ((6211409395973 / 500000000000) : ℝ) = ((500000000000 / 6211409395973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14201_neg : (1270747061 / 500000000) ≤ -Real.log (250000000000 / 3174657534247) ∧
    -Real.log (250000000000 / 3174657534247) ≤ (1270747063 / 500000000) := by
  have h := checkLog_sound (w := (1174657534247 / 5174657534247)) (n := 12)
    (lo := (231026291 / 500000000)) (hi := (462052583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3174657534247 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(3174657534247 / 2000000000000) = 1/(250000000000 / 3174657534247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14201 : Bounds (1270747061 / 500000000) (1270747063 / 500000000) (Real.log (3174657534247 / 250000000000)) := by
  have h := reflection_log_14201_neg
  have he : Real.log (3174657534247 / 250000000000) = -Real.log (250000000000 / 3174657534247) := by
    rw [show ((3174657534247 / 250000000000) : ℝ) = ((250000000000 / 3174657534247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14202_neg : (309481141 / 500000000) ≤ -Real.log (1000 / 1857) ∧
    -Real.log (1000 / 1857) ≤ (618962283 / 1000000000) := by
  have h := checkLog_sound (w := (857 / 2857)) (n := 12)
    (lo := (309481141 / 500000000)) (hi := (618962283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1857 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1857 / 1000) = 1/(1000 / 1857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14202 : Bounds (309481141 / 500000000) (618962283 / 1000000000) (Real.log (1857 / 1000)) := by
  have h := reflection_log_14202_neg
  have he : Real.log (1857 / 1000) = -Real.log (1000 / 1857) := by
    rw [show ((1857 / 1000) : ℝ) = ((1000 / 1857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14203_neg : (1944910647 / 1000000000) ≤ -Real.log (143 / 1000) ∧
    -Real.log (143 / 1000) ≤ (38898213 / 20000000) := by
  have h := checkLog_sound (w := (107 / 393)) (n := 12)
    (lo := (558616287 / 1000000000)) (hi := (17456759 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 143) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250 / 143) = 1/(143 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14203 : Bounds (-38898213 / 20000000) (-1944910647 / 1000000000) (Real.log (143 / 1000)) := by
  have h := reflection_log_14203_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14204_neg : (107079 / 125000000) ≤ -Real.log (1000000 / 1000857) ∧
    -Real.log (1000000 / 1000857) ≤ (856633 / 1000000000) := by
  have h := checkLog_sound (w := (857 / 2000857)) (n := 12)
    (lo := (107079 / 125000000)) (hi := (856633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000857 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000857 / 1000000) = 1/(1000000 / 1000857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14204 : Bounds (107079 / 125000000) (856633 / 1000000000) (Real.log (1000857 / 1000000)) := by
  have h := reflection_log_14204_neg
  have he : Real.log (1000857 / 1000000) = -Real.log (1000000 / 1000857) := by
    rw [show ((1000857 / 1000000) : ℝ) = ((1000000 / 1000857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14205_neg : (857367 / 1000000000) ≤ -Real.log (999143 / 1000000) ∧
    -Real.log (999143 / 1000000) ≤ (107171 / 125000000) := by
  have h := checkLog_sound (w := (857 / 1999143)) (n := 12)
    (lo := (857367 / 1000000000)) (hi := (107171 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999143) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999143) = 1/(999143 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14205 : Bounds (-107171 / 125000000) (-857367 / 1000000000) (Real.log (999143 / 1000000)) := by
  have h := reflection_log_14205_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_14206_neg : (406641083 / 1000000000) ≤ -Real.log (200000 / 300353) ∧
    -Real.log (200000 / 300353) ≤ (101660271 / 250000000) := by
  have h := checkLog_sound (w := (100353 / 500353)) (n := 12)
    (lo := (406641083 / 1000000000)) (hi := (101660271 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((300353 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(300353 / 200000) = 1/(200000 / 300353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14206 : Bounds (406641083 / 1000000000) (101660271 / 250000000) (Real.log (300353 / 200000)) := by
  have h := reflection_log_14206_neg
  have he : Real.log (300353 / 200000) = -Real.log (200000 / 300353) := by
    rw [show ((300353 / 200000) : ℝ) = ((200000 / 300353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14207_neg : (27867337 / 40000000) ≤ -Real.log (99647 / 200000) ∧
    -Real.log (99647 / 200000) ≤ (696683427 / 1000000000) := by
  have h := checkLog_sound (w := (353 / 199647)) (n := 12)
    (lo := (707249 / 200000000)) (hi := (1768123 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99647) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 99647) = 1/(99647 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14207 : Bounds (-696683427 / 1000000000) (-27867337 / 40000000) (Real.log (99647 / 200000)) := by
  have h := reflection_log_14207_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily
