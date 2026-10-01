import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1152_neg : (82818723 / 1000000000) ≤ -Real.log (460259 / 500000) ∧
    -Real.log (460259 / 500000) ≤ (20704681 / 250000000) := by
  have h := checkLog_sound (w := (39741 / 960259)) (n := 12)
    (lo := (82818723 / 1000000000)) (hi := (20704681 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460259) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460259) = 1/(460259 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1152 : Bounds (-20704681 / 250000000) (-82818723 / 1000000000) (Real.log (460259 / 500000)) := by
  have h := reflection_log_1152_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1153_neg : (76674889 / 1000000000) ≤ -Real.log (1000000 / 1079691) ∧
    -Real.log (1000000 / 1079691) ≤ (7667489 / 100000000) := by
  have h := checkLog_sound (w := (79691 / 2079691)) (n := 12)
    (lo := (76674889 / 1000000000)) (hi := (7667489 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079691 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079691 / 1000000) = 1/(1000000 / 1079691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1153 : Bounds (76674889 / 1000000000) (7667489 / 100000000) (Real.log (1079691 / 1000000)) := by
  have h := reflection_log_1153_neg
  have he : Real.log (1079691 / 1000000) = -Real.log (1000000 / 1079691) := by
    rw [show ((1079691 / 1000000) : ℝ) = ((1000000 / 1079691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1154_neg : (16609159 / 200000000) ≤ -Real.log (920309 / 1000000) ∧
    -Real.log (920309 / 1000000) ≤ (20761449 / 250000000) := by
  have h := checkLog_sound (w := (79691 / 1920309)) (n := 12)
    (lo := (16609159 / 200000000)) (hi := (20761449 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920309) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920309) = 1/(920309 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1154 : Bounds (-20761449 / 250000000) (-16609159 / 200000000) (Real.log (920309 / 1000000)) := by
  have h := reflection_log_1154_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1155_neg : (3185453 / 500000000) ≤ -Real.log (993649344519 / 1000000000000) ∧
    -Real.log (993649344519 / 1000000000000) ≤ (6370907 / 1000000000) := by
  have h := checkLog_sound (w := (6350655481 / 1993649344519)) (n := 12)
    (lo := (3185453 / 500000000)) (hi := (6370907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993649344519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993649344519) = 1/(993649344519 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1155 : Bounds (-6370907 / 1000000000) (-3185453 / 500000000) (Real.log (993649344519 / 1000000000000)) := by
  have h := reflection_log_1155_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1156_neg : (6337427 / 1000000000) ≤ -Real.log (248420652919 / 250000000000) ∧
    -Real.log (248420652919 / 250000000000) ≤ (1584357 / 250000000) := by
  have h := checkLog_sound (w := (1579347081 / 498420652919)) (n := 12)
    (lo := (6337427 / 1000000000)) (hi := (1584357 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248420652919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248420652919) = 1/(248420652919 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1156 : Bounds (-1584357 / 250000000) (-6337427 / 1000000000) (Real.log (248420652919 / 250000000000)) := by
  have h := reflection_log_1156_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1157_neg : (7965001 / 50000000) ≤ -Real.log (500000000000 / 586344862349) ∧
    -Real.log (500000000000 / 586344862349) ≤ (159300021 / 1000000000) := by
  have h := checkLog_sound (w := (86344862349 / 1086344862349)) (n := 12)
    (lo := (7965001 / 50000000)) (hi := (159300021 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586344862349 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586344862349 / 500000000000) = 1/(500000000000 / 586344862349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1157 : Bounds (7965001 / 50000000) (159300021 / 1000000000) (Real.log (586344862349 / 500000000000)) := by
  have h := reflection_log_1157_neg
  have he : Real.log (586344862349 / 500000000000) = -Real.log (500000000000 / 586344862349) := by
    rw [show ((586344862349 / 500000000000) : ℝ) = ((500000000000 / 586344862349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1158_neg : (39930171 / 250000000) ≤ -Real.log (250000000000 / 293295784351) ∧
    -Real.log (250000000000 / 293295784351) ≤ (31944137 / 200000000) := by
  have h := checkLog_sound (w := (43295784351 / 543295784351)) (n := 12)
    (lo := (39930171 / 250000000)) (hi := (31944137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293295784351 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293295784351 / 250000000000) = 1/(250000000000 / 293295784351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1158 : Bounds (39930171 / 250000000) (31944137 / 200000000) (Real.log (293295784351 / 250000000000)) := by
  have h := reflection_log_1158_neg
  have he : Real.log (293295784351 / 250000000000) = -Real.log (250000000000 / 293295784351) := by
    rw [show ((293295784351 / 250000000000) : ℝ) = ((250000000000 / 293295784351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1159_neg : (319490179 / 1000000000) ≤ -Real.log (125000000000 / 172053231939) ∧
    -Real.log (125000000000 / 172053231939) ≤ (15974509 / 50000000) := by
  have h := checkLog_sound (w := (47053231939 / 297053231939)) (n := 12)
    (lo := (319490179 / 1000000000)) (hi := (15974509 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172053231939 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172053231939 / 125000000000) = 1/(125000000000 / 172053231939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1159 : Bounds (319490179 / 1000000000) (15974509 / 50000000) (Real.log (172053231939 / 125000000000)) := by
  have h := reflection_log_1159_neg
  have he : Real.log (172053231939 / 125000000000) = -Real.log (125000000000 / 172053231939) := by
    rw [show ((172053231939 / 125000000000) : ℝ) = ((125000000000 / 172053231939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1160_neg : (31969533 / 100000000) ≤ -Real.log (500000000000 / 688354129531) ∧
    -Real.log (500000000000 / 688354129531) ≤ (319695331 / 1000000000) := by
  have h := checkLog_sound (w := (188354129531 / 1188354129531)) (n := 12)
    (lo := (31969533 / 100000000)) (hi := (319695331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((688354129531 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(688354129531 / 500000000000) = 1/(500000000000 / 688354129531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1160 : Bounds (31969533 / 100000000) (319695331 / 1000000000) (Real.log (688354129531 / 500000000000)) := by
  have h := reflection_log_1160_neg
  have he : Real.log (688354129531 / 500000000000) = -Real.log (500000000000 / 688354129531) := by
    rw [show ((688354129531 / 500000000000) : ℝ) = ((500000000000 / 688354129531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1161_neg : (147212379 / 1000000000) ≤ -Real.log (5000 / 5793) ∧
    -Real.log (5000 / 5793) ≤ (7360619 / 50000000) := by
  have h := checkLog_sound (w := (793 / 10793)) (n := 12)
    (lo := (147212379 / 1000000000)) (hi := (7360619 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5793 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5793 / 5000) = 1/(5000 / 5793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1161 : Bounds (147212379 / 1000000000) (7360619 / 50000000) (Real.log (5793 / 5000)) := by
  have h := reflection_log_1161_neg
  have he : Real.log (5793 / 5000) = -Real.log (5000 / 5793) := by
    rw [show ((5793 / 5000) : ℝ) = ((5000 / 5793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1162_neg : (172688107 / 1000000000) ≤ -Real.log (4207 / 5000) ∧
    -Real.log (4207 / 5000) ≤ (43172027 / 250000000) := by
  have h := checkLog_sound (w := (793 / 9207)) (n := 12)
    (lo := (172688107 / 1000000000)) (hi := (43172027 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4207) = 1/(4207 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1162 : Bounds (-43172027 / 250000000) (-172688107 / 1000000000) (Real.log (4207 / 5000)) := by
  have h := reflection_log_1162_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1163_neg : (158587 / 1000000000) ≤ -Real.log (5000000 / 5000793) ∧
    -Real.log (5000000 / 5000793) ≤ (39647 / 250000000) := by
  have h := checkLog_sound (w := (793 / 10000793)) (n := 12)
    (lo := (158587 / 1000000000)) (hi := (39647 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000793 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000793 / 5000000) = 1/(5000000 / 5000793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1163 : Bounds (158587 / 1000000000) (39647 / 250000000) (Real.log (5000793 / 5000000)) := by
  have h := reflection_log_1163_neg
  have he : Real.log (5000793 / 5000000) = -Real.log (5000000 / 5000793) := by
    rw [show ((5000793 / 5000000) : ℝ) = ((5000000 / 5000793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1164_neg : (39653 / 250000000) ≤ -Real.log (4999207 / 5000000) ∧
    -Real.log (4999207 / 5000000) ≤ (158613 / 1000000000) := by
  have h := checkLog_sound (w := (793 / 9999207)) (n := 12)
    (lo := (39653 / 250000000)) (hi := (158613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999207) = 1/(4999207 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1164 : Bounds (-158613 / 1000000000) (-39653 / 250000000) (Real.log (4999207 / 5000000)) := by
  have h := reflection_log_1164_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1165_neg : (76527613 / 1000000000) ≤ -Real.log (250000 / 269883) ∧
    -Real.log (250000 / 269883) ≤ (38263807 / 500000000) := by
  have h := checkLog_sound (w := (19883 / 519883)) (n := 12)
    (lo := (76527613 / 1000000000)) (hi := (38263807 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269883 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269883 / 250000) = 1/(250000 / 269883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1165 : Bounds (76527613 / 1000000000) (38263807 / 500000000) (Real.log (269883 / 250000)) := by
  have h := reflection_log_1165_neg
  have he : Real.log (269883 / 250000) = -Real.log (250000 / 269883) := by
    rw [show ((269883 / 250000) : ℝ) = ((250000 / 269883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1166_neg : (41436521 / 500000000) ≤ -Real.log (230117 / 250000) ∧
    -Real.log (230117 / 250000) ≤ (82873043 / 1000000000) := by
  have h := checkLog_sound (w := (19883 / 480117)) (n := 12)
    (lo := (41436521 / 500000000)) (hi := (82873043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230117) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230117) = 1/(230117 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1166 : Bounds (-82873043 / 1000000000) (-41436521 / 500000000) (Real.log (230117 / 250000)) := by
  have h := reflection_log_1166_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1167_neg : (76722123 / 1000000000) ≤ -Real.log (500000 / 539871) ∧
    -Real.log (500000 / 539871) ≤ (19180531 / 250000000) := by
  have h := checkLog_sound (w := (39871 / 1039871)) (n := 12)
    (lo := (76722123 / 1000000000)) (hi := (19180531 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539871 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539871 / 500000) = 1/(500000 / 539871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1167 : Bounds (76722123 / 1000000000) (19180531 / 250000000) (Real.log (539871 / 500000)) := by
  have h := reflection_log_1167_neg
  have he : Real.log (539871 / 500000) = -Real.log (500000 / 539871) := by
    rw [show ((539871 / 500000) : ℝ) = ((500000 / 539871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1168_neg : (83101213 / 1000000000) ≤ -Real.log (460129 / 500000) ∧
    -Real.log (460129 / 500000) ≤ (41550607 / 500000000) := by
  have h := checkLog_sound (w := (39871 / 960129)) (n := 12)
    (lo := (83101213 / 1000000000)) (hi := (41550607 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460129) = 1/(460129 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1168 : Bounds (-41550607 / 500000000) (-83101213 / 1000000000) (Real.log (460129 / 500000)) := by
  have h := reflection_log_1168_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1169_neg : (6379089 / 1000000000) ≤ -Real.log (248410303359 / 250000000000) ∧
    -Real.log (248410303359 / 250000000000) ≤ (637909 / 100000000) := by
  have h := checkLog_sound (w := (1589696641 / 498410303359)) (n := 12)
    (lo := (6379089 / 1000000000)) (hi := (637909 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248410303359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248410303359) = 1/(248410303359 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1169 : Bounds (-637909 / 100000000) (-6379089 / 1000000000) (Real.log (248410303359 / 250000000000)) := by
  have h := reflection_log_1169_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1170_neg : (1586357 / 250000000) ≤ -Real.log (62104666311 / 62500000000) ∧
    -Real.log (62104666311 / 62500000000) ≤ (6345429 / 1000000000) := by
  have h := checkLog_sound (w := (395333689 / 124604666311)) (n := 12)
    (lo := (1586357 / 250000000)) (hi := (6345429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62104666311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62104666311) = 1/(62104666311 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1170 : Bounds (-6345429 / 1000000000) (-1586357 / 250000000) (Real.log (62104666311 / 62500000000)) := by
  have h := reflection_log_1170_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1171_neg : (9962541 / 62500000) ≤ -Real.log (125000000000 / 146600968203) ∧
    -Real.log (125000000000 / 146600968203) ≤ (159400657 / 1000000000) := by
  have h := checkLog_sound (w := (21600968203 / 271600968203)) (n := 12)
    (lo := (9962541 / 62500000)) (hi := (159400657 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((146600968203 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(146600968203 / 125000000000) = 1/(125000000000 / 146600968203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1171 : Bounds (9962541 / 62500000) (159400657 / 1000000000) (Real.log (146600968203 / 125000000000)) := by
  have h := reflection_log_1171_neg
  have he : Real.log (146600968203 / 125000000000) = -Real.log (125000000000 / 146600968203) := by
    rw [show ((146600968203 / 125000000000) : ℝ) = ((125000000000 / 146600968203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1172_neg : (159823337 / 1000000000) ≤ -Real.log (250000000000 / 293325893391) ∧
    -Real.log (250000000000 / 293325893391) ≤ (79911669 / 500000000) := by
  have h := checkLog_sound (w := (43325893391 / 543325893391)) (n := 12)
    (lo := (159823337 / 1000000000)) (hi := (79911669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293325893391 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293325893391 / 250000000000) = 1/(250000000000 / 293325893391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1172 : Bounds (159823337 / 1000000000) (79911669 / 500000000) (Real.log (293325893391 / 250000000000)) := by
  have h := reflection_log_1172_neg
  have he : Real.log (293325893391 / 250000000000) = -Real.log (250000000000 / 293325893391) := by
    rw [show ((293325893391 / 250000000000) : ℝ) = ((250000000000 / 293325893391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1173_neg : (31969533 / 100000000) ≤ -Real.log (50000000000 / 68835412953) ∧
    -Real.log (50000000000 / 68835412953) ≤ (319695331 / 1000000000) := by
  have h := checkLog_sound (w := (18835412953 / 118835412953)) (n := 12)
    (lo := (31969533 / 100000000)) (hi := (319695331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68835412953 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68835412953 / 50000000000) = 1/(50000000000 / 68835412953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1173 : Bounds (31969533 / 100000000) (319695331 / 1000000000) (Real.log (68835412953 / 50000000000)) := by
  have h := reflection_log_1173_neg
  have he : Real.log (68835412953 / 50000000000) = -Real.log (50000000000 / 68835412953) := by
    rw [show ((68835412953 / 50000000000) : ℝ) = ((50000000000 / 68835412953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1174_neg : (319900487 / 1000000000) ≤ -Real.log (500000000000 / 688495364869) ∧
    -Real.log (500000000000 / 688495364869) ≤ (39987561 / 125000000) := by
  have h := checkLog_sound (w := (188495364869 / 1188495364869)) (n := 12)
    (lo := (319900487 / 1000000000)) (hi := (39987561 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((688495364869 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(688495364869 / 500000000000) = 1/(500000000000 / 688495364869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1174 : Bounds (319900487 / 1000000000) (39987561 / 125000000) (Real.log (688495364869 / 500000000000)) := by
  have h := reflection_log_1174_neg
  have he : Real.log (688495364869 / 500000000000) = -Real.log (500000000000 / 688495364869) := by
    rw [show ((688495364869 / 500000000000) : ℝ) = ((500000000000 / 688495364869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1175_neg : (147298687 / 1000000000) ≤ -Real.log (10000 / 11587) ∧
    -Real.log (10000 / 11587) ≤ (1150771 / 7812500) := by
  have h := checkLog_sound (w := (1587 / 21587)) (n := 12)
    (lo := (147298687 / 1000000000)) (hi := (1150771 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11587 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11587 / 10000) = 1/(10000 / 11587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1175 : Bounds (147298687 / 1000000000) (1150771 / 7812500) (Real.log (11587 / 10000)) := by
  have h := reflection_log_1175_neg
  have he : Real.log (11587 / 10000) = -Real.log (10000 / 11587) := by
    rw [show ((11587 / 10000) : ℝ) = ((10000 / 11587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1176_neg : (43201741 / 250000000) ≤ -Real.log (8413 / 10000) ∧
    -Real.log (8413 / 10000) ≤ (34561393 / 200000000) := by
  have h := checkLog_sound (w := (1587 / 18413)) (n := 12)
    (lo := (43201741 / 250000000)) (hi := (34561393 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8413) = 1/(8413 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1176 : Bounds (-34561393 / 200000000) (-43201741 / 250000000) (Real.log (8413 / 10000)) := by
  have h := reflection_log_1176_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1177_neg : (158687 / 1000000000) ≤ -Real.log (10000000 / 10001587) ∧
    -Real.log (10000000 / 10001587) ≤ (4959 / 31250000) := by
  have h := checkLog_sound (w := (1587 / 20001587)) (n := 12)
    (lo := (158687 / 1000000000)) (hi := (4959 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001587 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001587 / 10000000) = 1/(10000000 / 10001587) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1177 : Bounds (158687 / 1000000000) (4959 / 31250000) (Real.log (10001587 / 10000000)) := by
  have h := reflection_log_1177_neg
  have he : Real.log (10001587 / 10000000) = -Real.log (10000000 / 10001587) := by
    rw [show ((10001587 / 10000000) : ℝ) = ((10000000 / 10001587) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1178_neg : (19839 / 125000000) ≤ -Real.log (9998413 / 10000000) ∧
    -Real.log (9998413 / 10000000) ≤ (158713 / 1000000000) := by
  have h := checkLog_sound (w := (1587 / 19998413)) (n := 12)
    (lo := (19839 / 125000000)) (hi := (158713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998413) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998413) = 1/(9998413 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1178 : Bounds (-158713 / 1000000000) (-19839 / 125000000) (Real.log (9998413 / 10000000)) := by
  have h := reflection_log_1178_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1179_neg : (15314971 / 200000000) ≤ -Real.log (1000000 / 1079583) ∧
    -Real.log (1000000 / 1079583) ≤ (9571857 / 125000000) := by
  have h := checkLog_sound (w := (79583 / 2079583)) (n := 12)
    (lo := (15314971 / 200000000)) (hi := (9571857 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079583 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079583 / 1000000) = 1/(1000000 / 1079583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1179 : Bounds (15314971 / 200000000) (9571857 / 125000000) (Real.log (1079583 / 1000000)) := by
  have h := reflection_log_1179_neg
  have he : Real.log (1079583 / 1000000) = -Real.log (1000000 / 1079583) := by
    rw [show ((1079583 / 1000000) : ℝ) = ((1000000 / 1079583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1180_neg : (1658569 / 20000000) ≤ -Real.log (920417 / 1000000) ∧
    -Real.log (920417 / 1000000) ≤ (82928451 / 1000000000) := by
  have h := checkLog_sound (w := (79583 / 1920417)) (n := 12)
    (lo := (1658569 / 20000000)) (hi := (82928451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920417) = 1/(920417 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1180 : Bounds (-82928451 / 1000000000) (-1658569 / 20000000) (Real.log (920417 / 1000000)) := by
  have h := reflection_log_1180_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1181_neg : (19192339 / 250000000) ≤ -Real.log (1000000 / 1079793) ∧
    -Real.log (1000000 / 1079793) ≤ (76769357 / 1000000000) := by
  have h := checkLog_sound (w := (79793 / 2079793)) (n := 12)
    (lo := (19192339 / 250000000)) (hi := (76769357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079793 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079793 / 1000000) = 1/(1000000 / 1079793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1181 : Bounds (19192339 / 250000000) (76769357 / 1000000000) (Real.log (1079793 / 1000000)) := by
  have h := reflection_log_1181_neg
  have he : Real.log (1079793 / 1000000) = -Real.log (1000000 / 1079793) := by
    rw [show ((1079793 / 1000000) : ℝ) = ((1000000 / 1079793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1182_neg : (41578317 / 500000000) ≤ -Real.log (920207 / 1000000) ∧
    -Real.log (920207 / 1000000) ≤ (16631327 / 200000000) := by
  have h := checkLog_sound (w := (79793 / 1920207)) (n := 12)
    (lo := (41578317 / 500000000)) (hi := (16631327 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920207) = 1/(920207 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1182 : Bounds (-16631327 / 200000000) (-41578317 / 500000000) (Real.log (920207 / 1000000)) := by
  have h := reflection_log_1182_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1183_neg : (3193639 / 500000000) ≤ -Real.log (993633077151 / 1000000000000) ∧
    -Real.log (993633077151 / 1000000000000) ≤ (6387279 / 1000000000) := by
  have h := checkLog_sound (w := (6366922849 / 1993633077151)) (n := 12)
    (lo := (3193639 / 500000000)) (hi := (6387279 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993633077151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993633077151) = 1/(993633077151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1183 : Bounds (-6387279 / 1000000000) (-3193639 / 500000000) (Real.log (993633077151 / 1000000000000)) := by
  have h := reflection_log_1183_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1184_neg : (1270719 / 200000000) ≤ -Real.log (993666546111 / 1000000000000) ∧
    -Real.log (993666546111 / 1000000000000) ≤ (1588399 / 250000000) := by
  have h := checkLog_sound (w := (6333453889 / 1993666546111)) (n := 12)
    (lo := (1270719 / 200000000)) (hi := (1588399 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993666546111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993666546111) = 1/(993666546111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1184 : Bounds (-1588399 / 250000000) (-1270719 / 200000000) (Real.log (993666546111 / 1000000000000)) := by
  have h := reflection_log_1184_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1185_neg : (79751653 / 500000000) ≤ -Real.log (500000000000 / 586464070089) ∧
    -Real.log (500000000000 / 586464070089) ≤ (159503307 / 1000000000) := by
  have h := checkLog_sound (w := (86464070089 / 1086464070089)) (n := 12)
    (lo := (79751653 / 500000000)) (hi := (159503307 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586464070089 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586464070089 / 500000000000) = 1/(500000000000 / 586464070089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1185 : Bounds (79751653 / 500000000) (159503307 / 1000000000) (Real.log (586464070089 / 500000000000)) := by
  have h := reflection_log_1185_neg
  have he : Real.log (586464070089 / 500000000000) = -Real.log (500000000000 / 586464070089) := by
    rw [show ((586464070089 / 500000000000) : ℝ) = ((500000000000 / 586464070089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1186_neg : (15992599 / 100000000) ≤ -Real.log (500000000000 / 586712011537) ∧
    -Real.log (500000000000 / 586712011537) ≤ (159925991 / 1000000000) := by
  have h := checkLog_sound (w := (86712011537 / 1086712011537)) (n := 12)
    (lo := (15992599 / 100000000)) (hi := (159925991 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586712011537 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586712011537 / 500000000000) = 1/(500000000000 / 586712011537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1186 : Bounds (15992599 / 100000000) (159925991 / 1000000000) (Real.log (586712011537 / 500000000000)) := by
  have h := reflection_log_1186_neg
  have he : Real.log (586712011537 / 500000000000) = -Real.log (500000000000 / 586712011537) := by
    rw [show ((586712011537 / 500000000000) : ℝ) = ((500000000000 / 586712011537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1187_neg : (319900487 / 1000000000) ≤ -Real.log (125000000000 / 172123841217) ∧
    -Real.log (125000000000 / 172123841217) ≤ (39987561 / 125000000) := by
  have h := checkLog_sound (w := (47123841217 / 297123841217)) (n := 12)
    (lo := (319900487 / 1000000000)) (hi := (39987561 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172123841217 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172123841217 / 125000000000) = 1/(125000000000 / 172123841217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1187 : Bounds (319900487 / 1000000000) (39987561 / 125000000) (Real.log (172123841217 / 125000000000)) := by
  have h := reflection_log_1187_neg
  have he : Real.log (172123841217 / 125000000000) = -Real.log (125000000000 / 172123841217) := by
    rw [show ((172123841217 / 125000000000) : ℝ) = ((125000000000 / 172123841217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1188_neg : (320105651 / 1000000000) ≤ -Real.log (250000000000 / 344318316891) ∧
    -Real.log (250000000000 / 344318316891) ≤ (80026413 / 250000000) := by
  have h := checkLog_sound (w := (94318316891 / 594318316891)) (n := 12)
    (lo := (320105651 / 1000000000)) (hi := (80026413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((344318316891 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(344318316891 / 250000000000) = 1/(250000000000 / 344318316891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1188 : Bounds (320105651 / 1000000000) (80026413 / 250000000) (Real.log (344318316891 / 250000000000)) := by
  have h := reflection_log_1188_neg
  have he : Real.log (344318316891 / 250000000000) = -Real.log (250000000000 / 344318316891) := by
    rw [show ((344318316891 / 250000000000) : ℝ) = ((250000000000 / 344318316891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1189_neg : (73692493 / 500000000) ≤ -Real.log (2500 / 2897) ∧
    -Real.log (2500 / 2897) ≤ (147384987 / 1000000000) := by
  have h := checkLog_sound (w := (397 / 5397)) (n := 12)
    (lo := (73692493 / 500000000)) (hi := (147384987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2897 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2897 / 2500) = 1/(2500 / 2897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1189 : Bounds (73692493 / 500000000) (147384987 / 1000000000) (Real.log (2897 / 2500)) := by
  have h := reflection_log_1189_neg
  have he : Real.log (2897 / 2500) = -Real.log (2500 / 2897) := by
    rw [show ((2897 / 2500) : ℝ) = ((2500 / 2897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1190_neg : (34585167 / 200000000) ≤ -Real.log (2103 / 2500) ∧
    -Real.log (2103 / 2500) ≤ (43231459 / 250000000) := by
  have h := checkLog_sound (w := (397 / 4603)) (n := 12)
    (lo := (34585167 / 200000000)) (hi := (43231459 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500 / 2103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500 / 2103) = 1/(2103 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1190 : Bounds (-43231459 / 250000000) (-34585167 / 200000000) (Real.log (2103 / 2500)) := by
  have h := reflection_log_1190_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1191_neg : (158787 / 1000000000) ≤ -Real.log (2500000 / 2500397) ∧
    -Real.log (2500000 / 2500397) ≤ (39697 / 250000000) := by
  have h := checkLog_sound (w := (397 / 5000397)) (n := 12)
    (lo := (158787 / 1000000000)) (hi := (39697 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500397 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500397 / 2500000) = 1/(2500000 / 2500397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1191 : Bounds (158787 / 1000000000) (39697 / 250000000) (Real.log (2500397 / 2500000)) := by
  have h := reflection_log_1191_neg
  have he : Real.log (2500397 / 2500000) = -Real.log (2500000 / 2500397) := by
    rw [show ((2500397 / 2500000) : ℝ) = ((2500000 / 2500397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1192_neg : (39703 / 250000000) ≤ -Real.log (2499603 / 2500000) ∧
    -Real.log (2499603 / 2500000) ≤ (158813 / 1000000000) := by
  have h := checkLog_sound (w := (397 / 4999603)) (n := 12)
    (lo := (39703 / 250000000)) (hi := (158813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2499603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2499603) = 1/(2499603 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1192 : Bounds (-158813 / 1000000000) (-39703 / 250000000) (Real.log (2499603 / 2500000)) := by
  have h := reflection_log_1192_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1193_neg : (38311047 / 500000000) ≤ -Real.log (500000 / 539817) ∧
    -Real.log (500000 / 539817) ≤ (15324419 / 200000000) := by
  have h := checkLog_sound (w := (39817 / 1039817)) (n := 12)
    (lo := (38311047 / 500000000)) (hi := (15324419 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539817 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539817 / 500000) = 1/(500000 / 539817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1193 : Bounds (38311047 / 500000000) (15324419 / 200000000) (Real.log (539817 / 500000)) := by
  have h := reflection_log_1193_neg
  have he : Real.log (539817 / 500000) = -Real.log (500000 / 539817) := by
    rw [show ((539817 / 500000) : ℝ) = ((500000 / 539817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1194_neg : (82983861 / 1000000000) ≤ -Real.log (460183 / 500000) ∧
    -Real.log (460183 / 500000) ≤ (41491931 / 500000000) := by
  have h := checkLog_sound (w := (39817 / 960183)) (n := 12)
    (lo := (82983861 / 1000000000)) (hi := (41491931 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460183) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460183) = 1/(460183 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1194 : Bounds (-41491931 / 500000000) (-82983861 / 1000000000) (Real.log (460183 / 500000)) := by
  have h := reflection_log_1194_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1195_neg : (3840783 / 50000000) ≤ -Real.log (1000000 / 1079843) ∧
    -Real.log (1000000 / 1079843) ≤ (76815661 / 1000000000) := by
  have h := checkLog_sound (w := (79843 / 2079843)) (n := 12)
    (lo := (3840783 / 50000000)) (hi := (76815661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079843 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079843 / 1000000) = 1/(1000000 / 1079843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1195 : Bounds (3840783 / 50000000) (76815661 / 1000000000) (Real.log (1079843 / 1000000)) := by
  have h := reflection_log_1195_neg
  have he : Real.log (1079843 / 1000000) = -Real.log (1000000 / 1079843) := by
    rw [show ((1079843 / 1000000) : ℝ) = ((1000000 / 1079843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1196_neg : (83210971 / 1000000000) ≤ -Real.log (920157 / 1000000) ∧
    -Real.log (920157 / 1000000) ≤ (20802743 / 250000000) := by
  have h := checkLog_sound (w := (79843 / 1920157)) (n := 12)
    (lo := (83210971 / 1000000000)) (hi := (20802743 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920157) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920157) = 1/(920157 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1196 : Bounds (-20802743 / 250000000) (-83210971 / 1000000000) (Real.log (920157 / 1000000)) := by
  have h := reflection_log_1196_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1197_neg : (6395311 / 1000000000) ≤ -Real.log (993625095351 / 1000000000000) ∧
    -Real.log (993625095351 / 1000000000000) ≤ (399707 / 62500000) := by
  have h := checkLog_sound (w := (6374904649 / 1993625095351)) (n := 12)
    (lo := (6395311 / 1000000000)) (hi := (399707 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993625095351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993625095351) = 1/(993625095351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1197 : Bounds (-399707 / 62500000) (-6395311 / 1000000000) (Real.log (993625095351 / 1000000000000)) := by
  have h := reflection_log_1197_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1198_neg : (6361767 / 1000000000) ≤ -Real.log (248414606511 / 250000000000) ∧
    -Real.log (248414606511 / 250000000000) ≤ (795221 / 125000000) := by
  have h := checkLog_sound (w := (1585393489 / 498414606511)) (n := 12)
    (lo := (6361767 / 1000000000)) (hi := (795221 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248414606511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248414606511) = 1/(248414606511 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1198 : Bounds (-795221 / 125000000) (-6361767 / 1000000000) (Real.log (248414606511 / 250000000000)) := by
  have h := reflection_log_1198_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1199_neg : (39901489 / 250000000) ≤ -Real.log (250000000000 / 293262137019) ∧
    -Real.log (250000000000 / 293262137019) ≤ (159605957 / 1000000000) := by
  have h := checkLog_sound (w := (43262137019 / 543262137019)) (n := 12)
    (lo := (39901489 / 250000000)) (hi := (159605957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293262137019 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293262137019 / 250000000000) = 1/(250000000000 / 293262137019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1199 : Bounds (39901489 / 250000000) (159605957 / 1000000000) (Real.log (293262137019 / 250000000000)) := by
  have h := reflection_log_1199_neg
  have he : Real.log (293262137019 / 250000000000) = -Real.log (250000000000 / 293262137019) := by
    rw [show ((293262137019 / 250000000000) : ℝ) = ((250000000000 / 293262137019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1200_neg : (160026631 / 1000000000) ≤ -Real.log (100000000000 / 117354212379) ∧
    -Real.log (100000000000 / 117354212379) ≤ (20003329 / 125000000) := by
  have h := checkLog_sound (w := (17354212379 / 217354212379)) (n := 12)
    (lo := (160026631 / 1000000000)) (hi := (20003329 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117354212379 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117354212379 / 100000000000) = 1/(100000000000 / 117354212379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1200 : Bounds (160026631 / 1000000000) (20003329 / 125000000) (Real.log (117354212379 / 100000000000)) := by
  have h := reflection_log_1200_neg
  have he : Real.log (117354212379 / 100000000000) = -Real.log (100000000000 / 117354212379) := by
    rw [show ((117354212379 / 100000000000) : ℝ) = ((100000000000 / 117354212379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1201_neg : (320105651 / 1000000000) ≤ -Real.log (500000000000 / 688636633781) ∧
    -Real.log (500000000000 / 688636633781) ≤ (80026413 / 250000000) := by
  have h := checkLog_sound (w := (188636633781 / 1188636633781)) (n := 12)
    (lo := (320105651 / 1000000000)) (hi := (80026413 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((688636633781 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(688636633781 / 500000000000) = 1/(500000000000 / 688636633781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1201 : Bounds (320105651 / 1000000000) (80026413 / 250000000) (Real.log (688636633781 / 500000000000)) := by
  have h := reflection_log_1201_neg
  have he : Real.log (688636633781 / 500000000000) = -Real.log (500000000000 / 688636633781) := by
    rw [show ((688636633781 / 500000000000) : ℝ) = ((500000000000 / 688636633781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1202_neg : (160155411 / 500000000) ≤ -Real.log (250000000000 / 344388968141) ∧
    -Real.log (250000000000 / 344388968141) ≤ (320310823 / 1000000000) := by
  have h := checkLog_sound (w := (94388968141 / 594388968141)) (n := 12)
    (lo := (160155411 / 500000000)) (hi := (320310823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((344388968141 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(344388968141 / 250000000000) = 1/(250000000000 / 344388968141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1202 : Bounds (160155411 / 500000000) (320310823 / 1000000000) (Real.log (344388968141 / 250000000000)) := by
  have h := reflection_log_1202_neg
  have he : Real.log (344388968141 / 250000000000) = -Real.log (250000000000 / 344388968141) := by
    rw [show ((344388968141 / 250000000000) : ℝ) = ((250000000000 / 344388968141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1203_neg : (147471279 / 1000000000) ≤ -Real.log (10000 / 11589) ∧
    -Real.log (10000 / 11589) ≤ (1843391 / 12500000) := by
  have h := checkLog_sound (w := (1589 / 21589)) (n := 12)
    (lo := (147471279 / 1000000000)) (hi := (1843391 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11589 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11589 / 10000) = 1/(10000 / 11589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1203 : Bounds (147471279 / 1000000000) (1843391 / 12500000) (Real.log (11589 / 10000)) := by
  have h := reflection_log_1203_neg
  have he : Real.log (11589 / 10000) = -Real.log (10000 / 11589) := by
    rw [show ((11589 / 10000) : ℝ) = ((10000 / 11589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1204_neg : (2163059 / 12500000) ≤ -Real.log (8411 / 10000) ∧
    -Real.log (8411 / 10000) ≤ (173044721 / 1000000000) := by
  have h := checkLog_sound (w := (1589 / 18411)) (n := 12)
    (lo := (2163059 / 12500000)) (hi := (173044721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8411) = 1/(8411 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1204 : Bounds (-173044721 / 1000000000) (-2163059 / 12500000) (Real.log (8411 / 10000)) := by
  have h := reflection_log_1204_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1205_neg : (158887 / 1000000000) ≤ -Real.log (10000000 / 10001589) ∧
    -Real.log (10000000 / 10001589) ≤ (19861 / 125000000) := by
  have h := checkLog_sound (w := (1589 / 20001589)) (n := 12)
    (lo := (158887 / 1000000000)) (hi := (19861 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001589 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001589 / 10000000) = 1/(10000000 / 10001589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1205 : Bounds (158887 / 1000000000) (19861 / 125000000) (Real.log (10001589 / 10000000)) := by
  have h := reflection_log_1205_neg
  have he : Real.log (10001589 / 10000000) = -Real.log (10000000 / 10001589) := by
    rw [show ((10001589 / 10000000) : ℝ) = ((10000000 / 10001589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1206_neg : (2483 / 15625000) ≤ -Real.log (9998411 / 10000000) ∧
    -Real.log (9998411 / 10000000) ≤ (158913 / 1000000000) := by
  have h := checkLog_sound (w := (1589 / 19998411)) (n := 12)
    (lo := (2483 / 15625000)) (hi := (158913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998411) = 1/(9998411 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1206 : Bounds (-158913 / 1000000000) (-2483 / 15625000) (Real.log (9998411 / 10000000)) := by
  have h := reflection_log_1206_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1207_neg : (15333681 / 200000000) ≤ -Real.log (250000 / 269921) ∧
    -Real.log (250000 / 269921) ≤ (38334203 / 500000000) := by
  have h := checkLog_sound (w := (19921 / 519921)) (n := 12)
    (lo := (15333681 / 200000000)) (hi := (38334203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269921 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269921 / 250000) = 1/(250000 / 269921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1207 : Bounds (15333681 / 200000000) (38334203 / 500000000) (Real.log (269921 / 250000)) := by
  have h := reflection_log_1207_neg
  have he : Real.log (269921 / 250000) = -Real.log (250000 / 269921) := by
    rw [show ((269921 / 250000) : ℝ) = ((250000 / 269921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1208_neg : (83038189 / 1000000000) ≤ -Real.log (230079 / 250000) ∧
    -Real.log (230079 / 250000) ≤ (8303819 / 100000000) := by
  have h := checkLog_sound (w := (19921 / 480079)) (n := 12)
    (lo := (83038189 / 1000000000)) (hi := (8303819 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230079) = 1/(230079 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1208 : Bounds (-8303819 / 100000000) (-83038189 / 1000000000) (Real.log (230079 / 250000)) := by
  have h := reflection_log_1208_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1209_neg : (9607861 / 125000000) ≤ -Real.log (500000 / 539947) ∧
    -Real.log (500000 / 539947) ≤ (76862889 / 1000000000) := by
  have h := checkLog_sound (w := (39947 / 1039947)) (n := 12)
    (lo := (9607861 / 125000000)) (hi := (76862889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539947 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539947 / 500000) = 1/(500000 / 539947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1209 : Bounds (9607861 / 125000000) (76862889 / 1000000000) (Real.log (539947 / 500000)) := by
  have h := reflection_log_1209_neg
  have he : Real.log (539947 / 500000) = -Real.log (500000 / 539947) := by
    rw [show ((539947 / 500000) : ℝ) = ((500000 / 539947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1210_neg : (41633199 / 500000000) ≤ -Real.log (460053 / 500000) ∧
    -Real.log (460053 / 500000) ≤ (83266399 / 1000000000) := by
  have h := checkLog_sound (w := (39947 / 960053)) (n := 12)
    (lo := (41633199 / 500000000)) (hi := (83266399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460053) = 1/(460053 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1210 : Bounds (-83266399 / 1000000000) (-41633199 / 500000000) (Real.log (460053 / 500000)) := by
  have h := reflection_log_1210_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1211_neg : (640351 / 100000000) ≤ -Real.log (248404237191 / 250000000000) ∧
    -Real.log (248404237191 / 250000000000) ≤ (6403511 / 1000000000) := by
  have h := checkLog_sound (w := (1595762809 / 498404237191)) (n := 12)
    (lo := (640351 / 100000000)) (hi := (6403511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248404237191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248404237191) = 1/(248404237191 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1211 : Bounds (-6403511 / 1000000000) (-640351 / 100000000) (Real.log (248404237191 / 250000000000)) := by
  have h := reflection_log_1211_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1212_neg : (6369783 / 1000000000) ≤ -Real.log (62103153759 / 62500000000) ∧
    -Real.log (62103153759 / 62500000000) ≤ (796223 / 125000000) := by
  have h := checkLog_sound (w := (396846241 / 124603153759)) (n := 12)
    (lo := (6369783 / 1000000000)) (hi := (796223 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62103153759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62103153759) = 1/(62103153759 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1212 : Bounds (-796223 / 125000000) (-6369783 / 1000000000) (Real.log (62103153759 / 62500000000)) := by
  have h := reflection_log_1212_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1213_neg : (31941319 / 200000000) ≤ -Real.log (100000000000 / 117316660799) ∧
    -Real.log (100000000000 / 117316660799) ≤ (39926649 / 250000000) := by
  have h := checkLog_sound (w := (17316660799 / 217316660799)) (n := 12)
    (lo := (31941319 / 200000000)) (hi := (39926649 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117316660799 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117316660799 / 100000000000) = 1/(100000000000 / 117316660799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1213 : Bounds (31941319 / 200000000) (39926649 / 250000000) (Real.log (117316660799 / 100000000000)) := by
  have h := reflection_log_1213_neg
  have he : Real.log (117316660799 / 100000000000) = -Real.log (100000000000 / 117316660799) := by
    rw [show ((117316660799 / 100000000000) : ℝ) = ((100000000000 / 117316660799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1214_neg : (80064643 / 500000000) ≤ -Real.log (15625000000 / 18338478121) ∧
    -Real.log (15625000000 / 18338478121) ≤ (160129287 / 1000000000) := by
  have h := checkLog_sound (w := (2713478121 / 33963478121)) (n := 12)
    (lo := (80064643 / 500000000)) (hi := (160129287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18338478121 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18338478121 / 15625000000) = 1/(15625000000 / 18338478121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1214 : Bounds (80064643 / 500000000) (160129287 / 1000000000) (Real.log (18338478121 / 15625000000)) := by
  have h := reflection_log_1214_neg
  have he : Real.log (18338478121 / 15625000000) = -Real.log (15625000000 / 18338478121) := by
    rw [show ((18338478121 / 15625000000) : ℝ) = ((15625000000 / 18338478121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1215_neg : (160155411 / 500000000) ≤ -Real.log (500000000000 / 688777936281) ∧
    -Real.log (500000000000 / 688777936281) ≤ (320310823 / 1000000000) := by
  have h := checkLog_sound (w := (188777936281 / 1188777936281)) (n := 12)
    (lo := (160155411 / 500000000)) (hi := (320310823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((688777936281 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(688777936281 / 500000000000) = 1/(500000000000 / 688777936281) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1215 : Bounds (160155411 / 500000000) (320310823 / 1000000000) (Real.log (688777936281 / 500000000000)) := by
  have h := reflection_log_1215_neg
  have he : Real.log (688777936281 / 500000000000) = -Real.log (500000000000 / 688777936281) := by
    rw [show ((688777936281 / 500000000000) : ℝ) = ((500000000000 / 688777936281) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
