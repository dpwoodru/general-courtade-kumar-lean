import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1216_neg : (320515999 / 1000000000) ≤ -Real.log (250000000000 / 344459636191) ∧
    -Real.log (250000000000 / 344459636191) ≤ (80129 / 250000) := by
  have h := checkLog_sound (w := (94459636191 / 594459636191)) (n := 12)
    (lo := (320515999 / 1000000000)) (hi := (80129 / 250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((344459636191 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(344459636191 / 250000000000) = 1/(250000000000 / 344459636191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1216 : Bounds (320515999 / 1000000000) (80129 / 250000) (Real.log (344459636191 / 250000000000)) := by
  have h := reflection_log_1216_neg
  have he : Real.log (344459636191 / 250000000000) = -Real.log (250000000000 / 344459636191) := by
    rw [show ((344459636191 / 250000000000) : ℝ) = ((250000000000 / 344459636191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1217_neg : (36889391 / 250000000) ≤ -Real.log (1000 / 1159) ∧
    -Real.log (1000 / 1159) ≤ (29511513 / 200000000) := by
  have h := checkLog_sound (w := (159 / 2159)) (n := 12)
    (lo := (36889391 / 250000000)) (hi := (29511513 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1159 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1159 / 1000) = 1/(1000 / 1159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1217 : Bounds (36889391 / 250000000) (29511513 / 200000000) (Real.log (1159 / 1000)) := by
  have h := reflection_log_1217_neg
  have he : Real.log (1159 / 1000) = -Real.log (1000 / 1159) := by
    rw [show ((1159 / 1000) : ℝ) = ((1000 / 1159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1218_neg : (173163619 / 1000000000) ≤ -Real.log (841 / 1000) ∧
    -Real.log (841 / 1000) ≤ (8658181 / 50000000) := by
  have h := checkLog_sound (w := (159 / 1841)) (n := 12)
    (lo := (173163619 / 1000000000)) (hi := (8658181 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 841) = 1/(841 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1218 : Bounds (-8658181 / 50000000) (-173163619 / 1000000000) (Real.log (841 / 1000)) := by
  have h := reflection_log_1218_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1219_neg : (158987 / 1000000000) ≤ -Real.log (1000000 / 1000159) ∧
    -Real.log (1000000 / 1000159) ≤ (39747 / 250000000) := by
  have h := checkLog_sound (w := (159 / 2000159)) (n := 12)
    (lo := (158987 / 1000000000)) (hi := (39747 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000159 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000159 / 1000000) = 1/(1000000 / 1000159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1219 : Bounds (158987 / 1000000000) (39747 / 250000000) (Real.log (1000159 / 1000000)) := by
  have h := reflection_log_1219_neg
  have he : Real.log (1000159 / 1000000) = -Real.log (1000000 / 1000159) := by
    rw [show ((1000159 / 1000000) : ℝ) = ((1000000 / 1000159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1220_neg : (39753 / 250000000) ≤ -Real.log (999841 / 1000000) ∧
    -Real.log (999841 / 1000000) ≤ (159013 / 1000000000) := by
  have h := checkLog_sound (w := (159 / 1999841)) (n := 12)
    (lo := (39753 / 250000000)) (hi := (159013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999841) = 1/(999841 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1220 : Bounds (-159013 / 1000000000) (-39753 / 250000000) (Real.log (999841 / 1000000)) := by
  have h := reflection_log_1220_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1221_neg : (1917891 / 25000000) ≤ -Real.log (200000 / 215947) ∧
    -Real.log (200000 / 215947) ≤ (76715641 / 1000000000) := by
  have h := checkLog_sound (w := (15947 / 415947)) (n := 12)
    (lo := (1917891 / 25000000)) (hi := (76715641 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215947 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215947 / 200000) = 1/(200000 / 215947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1221 : Bounds (1917891 / 25000000) (76715641 / 1000000000) (Real.log (215947 / 200000)) := by
  have h := reflection_log_1221_neg
  have he : Real.log (215947 / 200000) = -Real.log (200000 / 215947) := by
    rw [show ((215947 / 200000) : ℝ) = ((200000 / 215947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1222_neg : (41546803 / 500000000) ≤ -Real.log (184053 / 200000) ∧
    -Real.log (184053 / 200000) ≤ (83093607 / 1000000000) := by
  have h := checkLog_sound (w := (15947 / 384053)) (n := 12)
    (lo := (41546803 / 500000000)) (hi := (83093607 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184053) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184053) = 1/(184053 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1222 : Bounds (-83093607 / 1000000000) (-41546803 / 500000000) (Real.log (184053 / 200000)) := by
  have h := reflection_log_1222_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1223_neg : (76910113 / 1000000000) ≤ -Real.log (200000 / 215989) ∧
    -Real.log (200000 / 215989) ≤ (38455057 / 500000000) := by
  have h := checkLog_sound (w := (15989 / 415989)) (n := 12)
    (lo := (76910113 / 1000000000)) (hi := (38455057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((215989 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(215989 / 200000) = 1/(200000 / 215989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1223 : Bounds (76910113 / 1000000000) (38455057 / 500000000) (Real.log (215989 / 200000)) := by
  have h := reflection_log_1223_neg
  have he : Real.log (215989 / 200000) = -Real.log (200000 / 215989) := by
    rw [show ((215989 / 200000) : ℝ) = ((200000 / 215989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1224_neg : (20830457 / 250000000) ≤ -Real.log (184011 / 200000) ∧
    -Real.log (184011 / 200000) ≤ (83321829 / 1000000000) := by
  have h := checkLog_sound (w := (15989 / 384011)) (n := 12)
    (lo := (20830457 / 250000000)) (hi := (83321829 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 184011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 184011) = 1/(184011 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1224 : Bounds (-83321829 / 1000000000) (-20830457 / 250000000) (Real.log (184011 / 200000)) := by
  have h := reflection_log_1224_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1225_neg : (3205857 / 500000000) ≤ -Real.log (39744351879 / 40000000000) ∧
    -Real.log (39744351879 / 40000000000) ≤ (1282343 / 200000000) := by
  have h := checkLog_sound (w := (255648121 / 79744351879)) (n := 12)
    (lo := (3205857 / 500000000)) (hi := (1282343 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39744351879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39744351879) = 1/(39744351879 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1225 : Bounds (-1282343 / 200000000) (-3205857 / 500000000) (Real.log (39744351879 / 40000000000)) := by
  have h := reflection_log_1225_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1226_neg : (3188983 / 500000000) ≤ -Real.log (39745693191 / 40000000000) ∧
    -Real.log (39745693191 / 40000000000) ≤ (6377967 / 1000000000) := by
  have h := checkLog_sound (w := (254306809 / 79745693191)) (n := 12)
    (lo := (3188983 / 500000000)) (hi := (6377967 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39745693191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39745693191) = 1/(39745693191 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1226 : Bounds (-6377967 / 1000000000) (-3188983 / 500000000) (Real.log (39745693191 / 40000000000)) := by
  have h := reflection_log_1226_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1227_neg : (159809247 / 1000000000) ≤ -Real.log (500000000000 / 586643521159) ∧
    -Real.log (500000000000 / 586643521159) ≤ (4994039 / 31250000) := by
  have h := checkLog_sound (w := (86643521159 / 1086643521159)) (n := 12)
    (lo := (159809247 / 1000000000)) (hi := (4994039 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586643521159 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586643521159 / 500000000000) = 1/(500000000000 / 586643521159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1227 : Bounds (159809247 / 1000000000) (4994039 / 31250000) (Real.log (586643521159 / 500000000000)) := by
  have h := reflection_log_1227_neg
  have he : Real.log (586643521159 / 500000000000) = -Real.log (500000000000 / 586643521159) := by
    rw [show ((586643521159 / 500000000000) : ℝ) = ((500000000000 / 586643521159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1228_neg : (80115971 / 500000000) ≤ -Real.log (31250000000 / 36680721533) ∧
    -Real.log (31250000000 / 36680721533) ≤ (160231943 / 1000000000) := by
  have h := checkLog_sound (w := (5430721533 / 67930721533)) (n := 12)
    (lo := (80115971 / 500000000)) (hi := (160231943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36680721533 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(36680721533 / 31250000000) = 1/(31250000000 / 36680721533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1228 : Bounds (80115971 / 500000000) (160231943 / 1000000000) (Real.log (36680721533 / 31250000000)) := by
  have h := reflection_log_1228_neg
  have he : Real.log (36680721533 / 31250000000) = -Real.log (31250000000 / 36680721533) := by
    rw [show ((36680721533 / 31250000000) : ℝ) = ((31250000000 / 36680721533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1229_neg : (320515999 / 1000000000) ≤ -Real.log (500000000000 / 688919272381) ∧
    -Real.log (500000000000 / 688919272381) ≤ (80129 / 250000) := by
  have h := checkLog_sound (w := (188919272381 / 1188919272381)) (n := 12)
    (lo := (320515999 / 1000000000)) (hi := (80129 / 250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((688919272381 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(688919272381 / 500000000000) = 1/(500000000000 / 688919272381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1229 : Bounds (320515999 / 1000000000) (80129 / 250000) (Real.log (688919272381 / 500000000000)) := by
  have h := reflection_log_1229_neg
  have he : Real.log (688919272381 / 500000000000) = -Real.log (500000000000 / 688919272381) := by
    rw [show ((688919272381 / 500000000000) : ℝ) = ((500000000000 / 688919272381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1230_neg : (320721183 / 1000000000) ≤ -Real.log (500000000000 / 689060642093) ∧
    -Real.log (500000000000 / 689060642093) ≤ (10022537 / 31250000) := by
  have h := checkLog_sound (w := (189060642093 / 1189060642093)) (n := 12)
    (lo := (320721183 / 1000000000)) (hi := (10022537 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((689060642093 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(689060642093 / 500000000000) = 1/(500000000000 / 689060642093) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1230 : Bounds (320721183 / 1000000000) (10022537 / 31250000) (Real.log (689060642093 / 500000000000)) := by
  have h := reflection_log_1230_neg
  have he : Real.log (689060642093 / 500000000000) = -Real.log (500000000000 / 689060642093) := by
    rw [show ((689060642093 / 500000000000) : ℝ) = ((500000000000 / 689060642093) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1231_neg : (147643841 / 1000000000) ≤ -Real.log (10000 / 11591) ∧
    -Real.log (10000 / 11591) ≤ (73821921 / 500000000) := by
  have h := checkLog_sound (w := (1591 / 21591)) (n := 12)
    (lo := (147643841 / 1000000000)) (hi := (73821921 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11591 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11591 / 10000) = 1/(10000 / 11591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1231 : Bounds (147643841 / 1000000000) (73821921 / 500000000) (Real.log (11591 / 10000)) := by
  have h := reflection_log_1231_neg
  have he : Real.log (11591 / 10000) = -Real.log (10000 / 11591) := by
    rw [show ((11591 / 10000) : ℝ) = ((10000 / 11591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1232_neg : (43320633 / 250000000) ≤ -Real.log (8409 / 10000) ∧
    -Real.log (8409 / 10000) ≤ (173282533 / 1000000000) := by
  have h := checkLog_sound (w := (1591 / 18409)) (n := 12)
    (lo := (43320633 / 250000000)) (hi := (173282533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8409) = 1/(8409 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1232 : Bounds (-173282533 / 1000000000) (-43320633 / 250000000) (Real.log (8409 / 10000)) := by
  have h := reflection_log_1232_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1233_neg : (159087 / 1000000000) ≤ -Real.log (10000000 / 10001591) ∧
    -Real.log (10000000 / 10001591) ≤ (9943 / 62500000) := by
  have h := checkLog_sound (w := (1591 / 20001591)) (n := 12)
    (lo := (159087 / 1000000000)) (hi := (9943 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001591 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001591 / 10000000) = 1/(10000000 / 10001591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1233 : Bounds (159087 / 1000000000) (9943 / 62500000) (Real.log (10001591 / 10000000)) := by
  have h := reflection_log_1233_neg
  have he : Real.log (10001591 / 10000000) = -Real.log (10000000 / 10001591) := by
    rw [show ((10001591 / 10000000) : ℝ) = ((10000000 / 10001591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1234_neg : (19889 / 125000000) ≤ -Real.log (9998409 / 10000000) ∧
    -Real.log (9998409 / 10000000) ≤ (159113 / 1000000000) := by
  have h := checkLog_sound (w := (1591 / 19998409)) (n := 12)
    (lo := (19889 / 125000000)) (hi := (159113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998409) = 1/(9998409 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1234 : Bounds (-159113 / 1000000000) (-19889 / 125000000) (Real.log (9998409 / 10000000)) := by
  have h := reflection_log_1234_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1235_neg : (76762873 / 1000000000) ≤ -Real.log (500000 / 539893) ∧
    -Real.log (500000 / 539893) ≤ (38381437 / 500000000) := by
  have h := checkLog_sound (w := (39893 / 1039893)) (n := 12)
    (lo := (76762873 / 1000000000)) (hi := (38381437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((539893 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(539893 / 500000) = 1/(500000 / 539893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1235 : Bounds (76762873 / 1000000000) (38381437 / 500000000) (Real.log (539893 / 500000)) := by
  have h := reflection_log_1235_neg
  have he : Real.log (539893 / 500000) = -Real.log (500000 / 539893) := by
    rw [show ((539893 / 500000) : ℝ) = ((500000 / 539893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1236_neg : (83149027 / 1000000000) ≤ -Real.log (460107 / 500000) ∧
    -Real.log (460107 / 500000) ≤ (20787257 / 250000000) := by
  have h := checkLog_sound (w := (39893 / 960107)) (n := 12)
    (lo := (83149027 / 1000000000)) (hi := (20787257 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 460107) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 460107) = 1/(460107 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1236 : Bounds (-20787257 / 250000000) (-83149027 / 1000000000) (Real.log (460107 / 500000)) := by
  have h := reflection_log_1236_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1237_neg : (76957337 / 1000000000) ≤ -Real.log (250000 / 269999) ∧
    -Real.log (250000 / 269999) ≤ (38478669 / 500000000) := by
  have h := checkLog_sound (w := (19999 / 519999)) (n := 12)
    (lo := (76957337 / 1000000000)) (hi := (38478669 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269999 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269999 / 250000) = 1/(250000 / 269999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1237 : Bounds (76957337 / 1000000000) (38478669 / 500000000) (Real.log (269999 / 250000)) := by
  have h := reflection_log_1237_neg
  have he : Real.log (269999 / 250000) = -Real.log (250000 / 269999) := by
    rw [show ((269999 / 250000) : ℝ) = ((250000 / 269999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1238_neg : (83377261 / 1000000000) ≤ -Real.log (230001 / 250000) ∧
    -Real.log (230001 / 250000) ≤ (41688631 / 500000000) := by
  have h := checkLog_sound (w := (19999 / 480001)) (n := 12)
    (lo := (83377261 / 1000000000)) (hi := (41688631 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230001) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230001) = 1/(230001 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1238 : Bounds (-41688631 / 500000000) (-83377261 / 1000000000) (Real.log (230001 / 250000)) := by
  have h := reflection_log_1238_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1239_neg : (6419923 / 1000000000) ≤ -Real.log (62100039999 / 62500000000) ∧
    -Real.log (62100039999 / 62500000000) ≤ (1604981 / 250000000) := by
  have h := checkLog_sound (w := (399960001 / 124600039999)) (n := 12)
    (lo := (6419923 / 1000000000)) (hi := (1604981 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62100039999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62100039999) = 1/(62100039999 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1239 : Bounds (-1604981 / 250000000) (-6419923 / 1000000000) (Real.log (62100039999 / 62500000000)) := by
  have h := reflection_log_1239_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1240_neg : (6386153 / 1000000000) ≤ -Real.log (248408548551 / 250000000000) ∧
    -Real.log (248408548551 / 250000000000) ≤ (3193077 / 500000000) := by
  have h := checkLog_sound (w := (1591451449 / 498408548551)) (n := 12)
    (lo := (6386153 / 1000000000)) (hi := (3193077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248408548551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248408548551) = 1/(248408548551 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1240 : Bounds (-3193077 / 500000000) (-6386153 / 1000000000) (Real.log (248408548551 / 250000000000)) := by
  have h := reflection_log_1240_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1241_neg : (1599119 / 10000000) ≤ -Real.log (250000000000 / 293351872499) ∧
    -Real.log (250000000000 / 293351872499) ≤ (159911901 / 1000000000) := by
  have h := checkLog_sound (w := (43351872499 / 543351872499)) (n := 12)
    (lo := (1599119 / 10000000)) (hi := (159911901 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293351872499 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293351872499 / 250000000000) = 1/(250000000000 / 293351872499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1241 : Bounds (1599119 / 10000000) (159911901 / 1000000000) (Real.log (293351872499 / 250000000000)) := by
  have h := reflection_log_1241_neg
  have he : Real.log (293351872499 / 250000000000) = -Real.log (250000000000 / 293351872499) := by
    rw [show ((293351872499 / 250000000000) : ℝ) = ((250000000000 / 293351872499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1242_neg : (80167299 / 500000000) ≤ -Real.log (250000000000 / 293475897931) ∧
    -Real.log (250000000000 / 293475897931) ≤ (160334599 / 1000000000) := by
  have h := checkLog_sound (w := (43475897931 / 543475897931)) (n := 12)
    (lo := (80167299 / 500000000)) (hi := (160334599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293475897931 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293475897931 / 250000000000) = 1/(250000000000 / 293475897931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1242 : Bounds (80167299 / 500000000) (160334599 / 1000000000) (Real.log (293475897931 / 250000000000)) := by
  have h := reflection_log_1242_neg
  have he : Real.log (293475897931 / 250000000000) = -Real.log (250000000000 / 293475897931) := by
    rw [show ((293475897931 / 250000000000) : ℝ) = ((250000000000 / 293475897931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1243_neg : (320721183 / 1000000000) ≤ -Real.log (125000000000 / 172265160523) ∧
    -Real.log (125000000000 / 172265160523) ≤ (10022537 / 31250000) := by
  have h := checkLog_sound (w := (47265160523 / 297265160523)) (n := 12)
    (lo := (320721183 / 1000000000)) (hi := (10022537 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172265160523 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172265160523 / 125000000000) = 1/(125000000000 / 172265160523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1243 : Bounds (320721183 / 1000000000) (10022537 / 31250000) (Real.log (172265160523 / 125000000000)) := by
  have h := reflection_log_1243_neg
  have he : Real.log (172265160523 / 125000000000) = -Real.log (125000000000 / 172265160523) := by
    rw [show ((172265160523 / 125000000000) : ℝ) = ((125000000000 / 172265160523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1244_neg : (160463187 / 500000000) ≤ -Real.log (125000000000 / 172300511357) ∧
    -Real.log (125000000000 / 172300511357) ≤ (2567411 / 8000000) := by
  have h := checkLog_sound (w := (47300511357 / 297300511357)) (n := 12)
    (lo := (160463187 / 500000000)) (hi := (2567411 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((172300511357 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(172300511357 / 125000000000) = 1/(125000000000 / 172300511357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1244 : Bounds (160463187 / 500000000) (2567411 / 8000000) (Real.log (172300511357 / 125000000000)) := by
  have h := reflection_log_1244_neg
  have he : Real.log (172300511357 / 125000000000) = -Real.log (125000000000 / 172300511357) := by
    rw [show ((172300511357 / 125000000000) : ℝ) = ((125000000000 / 172300511357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1245_neg : (2308283 / 15625000) ≤ -Real.log (1250 / 1449) ∧
    -Real.log (1250 / 1449) ≤ (147730113 / 1000000000) := by
  have h := checkLog_sound (w := (199 / 2699)) (n := 12)
    (lo := (2308283 / 15625000)) (hi := (147730113 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1449 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1449 / 1250) = 1/(1250 / 1449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1245 : Bounds (2308283 / 15625000) (147730113 / 1000000000) (Real.log (1449 / 1250)) := by
  have h := reflection_log_1245_neg
  have he : Real.log (1449 / 1250) = -Real.log (1250 / 1449) := by
    rw [show ((1449 / 1250) : ℝ) = ((1250 / 1449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1246_neg : (173401459 / 1000000000) ≤ -Real.log (1051 / 1250) ∧
    -Real.log (1051 / 1250) ≤ (8670073 / 50000000) := by
  have h := checkLog_sound (w := (199 / 2301)) (n := 12)
    (lo := (173401459 / 1000000000)) (hi := (8670073 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1051) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1051) = 1/(1051 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1246 : Bounds (-8670073 / 50000000) (-173401459 / 1000000000) (Real.log (1051 / 1250)) := by
  have h := reflection_log_1246_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1247_neg : (159187 / 1000000000) ≤ -Real.log (1250000 / 1250199) ∧
    -Real.log (1250000 / 1250199) ≤ (39797 / 250000000) := by
  have h := checkLog_sound (w := (199 / 2500199)) (n := 12)
    (lo := (159187 / 1000000000)) (hi := (39797 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250199 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250199 / 1250000) = 1/(1250000 / 1250199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1247 : Bounds (159187 / 1000000000) (39797 / 250000000) (Real.log (1250199 / 1250000)) := by
  have h := reflection_log_1247_neg
  have he : Real.log (1250199 / 1250000) = -Real.log (1250000 / 1250199) := by
    rw [show ((1250199 / 1250000) : ℝ) = ((1250000 / 1250199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1248_neg : (39803 / 250000000) ≤ -Real.log (1249801 / 1250000) ∧
    -Real.log (1249801 / 1250000) ≤ (159213 / 1000000000) := by
  have h := checkLog_sound (w := (199 / 2499801)) (n := 12)
    (lo := (39803 / 250000000)) (hi := (159213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249801) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249801) = 1/(1249801 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1248 : Bounds (-159213 / 1000000000) (-39803 / 250000000) (Real.log (1249801 / 1250000)) := by
  have h := reflection_log_1248_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1249_neg : (76809177 / 1000000000) ≤ -Real.log (250000 / 269959) ∧
    -Real.log (250000 / 269959) ≤ (38404589 / 500000000) := by
  have h := checkLog_sound (w := (19959 / 519959)) (n := 12)
    (lo := (76809177 / 1000000000)) (hi := (38404589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((269959 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(269959 / 250000) = 1/(250000 / 269959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1249 : Bounds (76809177 / 1000000000) (38404589 / 500000000) (Real.log (269959 / 250000)) := by
  have h := reflection_log_1249_neg
  have he : Real.log (269959 / 250000) = -Real.log (250000 / 269959) := by
    rw [show ((269959 / 250000) : ℝ) = ((250000 / 269959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1250_neg : (83203363 / 1000000000) ≤ -Real.log (230041 / 250000) ∧
    -Real.log (230041 / 250000) ≤ (20800841 / 250000000) := by
  have h := checkLog_sound (w := (19959 / 480041)) (n := 12)
    (lo := (83203363 / 1000000000)) (hi := (20800841 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 230041) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 230041) = 1/(230041 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1250 : Bounds (-20800841 / 250000000) (-83203363 / 1000000000) (Real.log (230041 / 250000)) := by
  have h := reflection_log_1250_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1251_neg : (4812727 / 62500000) ≤ -Real.log (500000 / 540023) ∧
    -Real.log (500000 / 540023) ≤ (77003633 / 1000000000) := by
  have h := checkLog_sound (w := (40023 / 1040023)) (n := 12)
    (lo := (4812727 / 62500000)) (hi := (77003633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((540023 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(540023 / 500000) = 1/(500000 / 540023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1251 : Bounds (4812727 / 62500000) (77003633 / 1000000000) (Real.log (540023 / 500000)) := by
  have h := reflection_log_1251_neg
  have he : Real.log (540023 / 500000) = -Real.log (500000 / 540023) := by
    rw [show ((540023 / 500000) : ℝ) = ((500000 / 540023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1252_neg : (8343161 / 100000000) ≤ -Real.log (459977 / 500000) ∧
    -Real.log (459977 / 500000) ≤ (83431611 / 1000000000) := by
  have h := checkLog_sound (w := (40023 / 959977)) (n := 12)
    (lo := (8343161 / 100000000)) (hi := (83431611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 459977) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 459977) = 1/(459977 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1252 : Bounds (-83431611 / 1000000000) (-8343161 / 100000000) (Real.log (459977 / 500000)) := by
  have h := reflection_log_1252_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1253_neg : (6427977 / 1000000000) ≤ -Real.log (248398159471 / 250000000000) ∧
    -Real.log (248398159471 / 250000000000) ≤ (3213989 / 500000000) := by
  have h := checkLog_sound (w := (1601840529 / 498398159471)) (n := 12)
    (lo := (6427977 / 1000000000)) (hi := (3213989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248398159471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248398159471) = 1/(248398159471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1253 : Bounds (-3213989 / 500000000) (-6427977 / 1000000000) (Real.log (248398159471 / 250000000000)) := by
  have h := reflection_log_1253_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1254_neg : (3197093 / 500000000) ≤ -Real.log (62101638319 / 62500000000) ∧
    -Real.log (62101638319 / 62500000000) ≤ (6394187 / 1000000000) := by
  have h := checkLog_sound (w := (398361681 / 124601638319)) (n := 12)
    (lo := (3197093 / 500000000)) (hi := (6394187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62101638319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62101638319) = 1/(62101638319 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1254 : Bounds (-6394187 / 1000000000) (-3197093 / 500000000) (Real.log (62101638319 / 62500000000)) := by
  have h := reflection_log_1254_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1255_neg : (160012541 / 1000000000) ≤ -Real.log (250000000000 / 293381397229) ∧
    -Real.log (250000000000 / 293381397229) ≤ (80006271 / 500000000) := by
  have h := checkLog_sound (w := (43381397229 / 543381397229)) (n := 12)
    (lo := (160012541 / 1000000000)) (hi := (80006271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293381397229 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293381397229 / 250000000000) = 1/(250000000000 / 293381397229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1255 : Bounds (160012541 / 1000000000) (80006271 / 500000000) (Real.log (293381397229 / 250000000000)) := by
  have h := reflection_log_1255_neg
  have he : Real.log (293381397229 / 250000000000) = -Real.log (250000000000 / 293381397229) := by
    rw [show ((293381397229 / 250000000000) : ℝ) = ((250000000000 / 293381397229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1256_neg : (160435243 / 1000000000) ≤ -Real.log (500000000000 / 587010872283) ∧
    -Real.log (500000000000 / 587010872283) ≤ (40108811 / 250000000) := by
  have h := checkLog_sound (w := (87010872283 / 1087010872283)) (n := 12)
    (lo := (160435243 / 1000000000)) (hi := (40108811 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587010872283 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587010872283 / 500000000000) = 1/(500000000000 / 587010872283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1256 : Bounds (160435243 / 1000000000) (40108811 / 250000000) (Real.log (587010872283 / 500000000000)) := by
  have h := reflection_log_1256_neg
  have he : Real.log (587010872283 / 500000000000) = -Real.log (500000000000 / 587010872283) := by
    rw [show ((587010872283 / 500000000000) : ℝ) = ((500000000000 / 587010872283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1257_neg : (160463187 / 500000000) ≤ -Real.log (500000000000 / 689202045427) ∧
    -Real.log (500000000000 / 689202045427) ≤ (2567411 / 8000000) := by
  have h := checkLog_sound (w := (189202045427 / 1189202045427)) (n := 12)
    (lo := (160463187 / 500000000)) (hi := (2567411 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((689202045427 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(689202045427 / 500000000000) = 1/(500000000000 / 689202045427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1257 : Bounds (160463187 / 500000000) (2567411 / 8000000) (Real.log (689202045427 / 500000000000)) := by
  have h := reflection_log_1257_neg
  have he : Real.log (689202045427 / 500000000000) = -Real.log (500000000000 / 689202045427) := by
    rw [show ((689202045427 / 500000000000) : ℝ) = ((500000000000 / 689202045427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1258_neg : (321131571 / 1000000000) ≤ -Real.log (250000000000 / 344671741199) ∧
    -Real.log (250000000000 / 344671741199) ≤ (80282893 / 250000000) := by
  have h := checkLog_sound (w := (94671741199 / 594671741199)) (n := 12)
    (lo := (321131571 / 1000000000)) (hi := (80282893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((344671741199 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(344671741199 / 250000000000) = 1/(250000000000 / 344671741199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1258 : Bounds (321131571 / 1000000000) (80282893 / 250000000) (Real.log (344671741199 / 250000000000)) := by
  have h := reflection_log_1258_neg
  have he : Real.log (344671741199 / 250000000000) = -Real.log (250000000000 / 344671741199) := by
    rw [show ((344671741199 / 250000000000) : ℝ) = ((250000000000 / 344671741199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1259_neg : (73908187 / 500000000) ≤ -Real.log (10000 / 11593) ∧
    -Real.log (10000 / 11593) ≤ (1182531 / 8000000) := by
  have h := checkLog_sound (w := (1593 / 21593)) (n := 12)
    (lo := (73908187 / 500000000)) (hi := (1182531 / 8000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11593 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11593 / 10000) = 1/(10000 / 11593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1259 : Bounds (73908187 / 500000000) (1182531 / 8000000) (Real.log (11593 / 10000)) := by
  have h := reflection_log_1259_neg
  have he : Real.log (11593 / 10000) = -Real.log (10000 / 11593) := by
    rw [show ((11593 / 10000) : ℝ) = ((10000 / 11593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1260_neg : (433801 / 2500000) ≤ -Real.log (8407 / 10000) ∧
    -Real.log (8407 / 10000) ≤ (173520401 / 1000000000) := by
  have h := checkLog_sound (w := (1593 / 18407)) (n := 12)
    (lo := (433801 / 2500000)) (hi := (173520401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8407) = 1/(8407 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1260 : Bounds (-173520401 / 1000000000) (-433801 / 2500000) (Real.log (8407 / 10000)) := by
  have h := reflection_log_1260_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1261_neg : (159287 / 1000000000) ≤ -Real.log (10000000 / 10001593) ∧
    -Real.log (10000000 / 10001593) ≤ (19911 / 125000000) := by
  have h := checkLog_sound (w := (1593 / 20001593)) (n := 12)
    (lo := (159287 / 1000000000)) (hi := (19911 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001593 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001593 / 10000000) = 1/(10000000 / 10001593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1261 : Bounds (159287 / 1000000000) (19911 / 125000000) (Real.log (10001593 / 10000000)) := by
  have h := reflection_log_1261_neg
  have he : Real.log (10001593 / 10000000) = -Real.log (10000000 / 10001593) := by
    rw [show ((10001593 / 10000000) : ℝ) = ((10000000 / 10001593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1262_neg : (9957 / 62500000) ≤ -Real.log (9998407 / 10000000) ∧
    -Real.log (9998407 / 10000000) ≤ (159313 / 1000000000) := by
  have h := checkLog_sound (w := (1593 / 19998407)) (n := 12)
    (lo := (9957 / 62500000)) (hi := (159313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998407) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998407) = 1/(9998407 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1262 : Bounds (-159313 / 1000000000) (-9957 / 62500000) (Real.log (9998407 / 10000000)) := by
  have h := reflection_log_1262_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1263_neg : (38428203 / 500000000) ≤ -Real.log (1000000 / 1079887) ∧
    -Real.log (1000000 / 1079887) ≤ (76856407 / 1000000000) := by
  have h := checkLog_sound (w := (79887 / 2079887)) (n := 12)
    (lo := (38428203 / 500000000)) (hi := (76856407 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079887 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079887 / 1000000) = 1/(1000000 / 1079887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1263 : Bounds (38428203 / 500000000) (76856407 / 1000000000) (Real.log (1079887 / 1000000)) := by
  have h := reflection_log_1263_neg
  have he : Real.log (1079887 / 1000000) = -Real.log (1000000 / 1079887) := by
    rw [show ((1079887 / 1000000) : ℝ) = ((1000000 / 1079887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1264_neg : (8325879 / 100000000) ≤ -Real.log (920113 / 1000000) ∧
    -Real.log (920113 / 1000000) ≤ (83258791 / 1000000000) := by
  have h := checkLog_sound (w := (79887 / 1920113)) (n := 12)
    (lo := (8325879 / 100000000)) (hi := (83258791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920113) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920113) = 1/(920113 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1264 : Bounds (-83258791 / 1000000000) (-8325879 / 100000000) (Real.log (920113 / 1000000)) := by
  have h := reflection_log_1264_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1265_neg : (77050851 / 1000000000) ≤ -Real.log (1000000 / 1080097) ∧
    -Real.log (1000000 / 1080097) ≤ (19262713 / 250000000) := by
  have h := checkLog_sound (w := (80097 / 2080097)) (n := 12)
    (lo := (77050851 / 1000000000)) (hi := (19262713 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1080097 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1080097 / 1000000) = 1/(1000000 / 1080097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1265 : Bounds (77050851 / 1000000000) (19262713 / 250000000) (Real.log (1080097 / 1000000)) := by
  have h := reflection_log_1265_neg
  have he : Real.log (1080097 / 1000000) = -Real.log (1000000 / 1080097) := by
    rw [show ((1080097 / 1000000) : ℝ) = ((1000000 / 1080097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1266_neg : (83487049 / 1000000000) ≤ -Real.log (919903 / 1000000) ∧
    -Real.log (919903 / 1000000) ≤ (1669741 / 20000000) := by
  have h := checkLog_sound (w := (80097 / 1919903)) (n := 12)
    (lo := (83487049 / 1000000000)) (hi := (1669741 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 919903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 919903) = 1/(919903 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1266 : Bounds (-1669741 / 20000000) (-83487049 / 1000000000) (Real.log (919903 / 1000000)) := by
  have h := reflection_log_1266_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1267_neg : (6436197 / 1000000000) ≤ -Real.log (993584470591 / 1000000000000) ∧
    -Real.log (993584470591 / 1000000000000) ≤ (3218099 / 500000000) := by
  have h := checkLog_sound (w := (6415529409 / 1993584470591)) (n := 12)
    (lo := (6436197 / 1000000000)) (hi := (3218099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993584470591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993584470591) = 1/(993584470591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1267 : Bounds (-3218099 / 500000000) (-6436197 / 1000000000) (Real.log (993584470591 / 1000000000000)) := by
  have h := reflection_log_1267_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1268_neg : (400149 / 62500000) ≤ -Real.log (993618067231 / 1000000000000) ∧
    -Real.log (993618067231 / 1000000000000) ≤ (1280477 / 200000000) := by
  have h := checkLog_sound (w := (6381932769 / 1993618067231)) (n := 12)
    (lo := (400149 / 62500000)) (hi := (1280477 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993618067231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993618067231) = 1/(993618067231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1268 : Bounds (-1280477 / 200000000) (-400149 / 62500000) (Real.log (993618067231 / 1000000000000)) := by
  have h := reflection_log_1268_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1269_neg : (40028799 / 250000000) ≤ -Real.log (250000000000 / 293411515759) ∧
    -Real.log (250000000000 / 293411515759) ≤ (160115197 / 1000000000) := by
  have h := checkLog_sound (w := (43411515759 / 543411515759)) (n := 12)
    (lo := (40028799 / 250000000)) (hi := (160115197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293411515759 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293411515759 / 250000000000) = 1/(250000000000 / 293411515759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1269 : Bounds (40028799 / 250000000) (160115197 / 1000000000) (Real.log (293411515759 / 250000000000)) := by
  have h := reflection_log_1269_neg
  have he : Real.log (293411515759 / 250000000000) = -Real.log (250000000000 / 293411515759) := by
    rw [show ((293411515759 / 250000000000) : ℝ) = ((250000000000 / 293411515759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1270_neg : (160537901 / 1000000000) ≤ -Real.log (500000000000 / 587071136849) ∧
    -Real.log (500000000000 / 587071136849) ≤ (80268951 / 500000000) := by
  have h := checkLog_sound (w := (87071136849 / 1087071136849)) (n := 12)
    (lo := (160537901 / 1000000000)) (hi := (80268951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587071136849 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587071136849 / 500000000000) = 1/(500000000000 / 587071136849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1270 : Bounds (160537901 / 1000000000) (80268951 / 500000000) (Real.log (587071136849 / 500000000000)) := by
  have h := reflection_log_1270_neg
  have he : Real.log (587071136849 / 500000000000) = -Real.log (500000000000 / 587071136849) := by
    rw [show ((587071136849 / 500000000000) : ℝ) = ((500000000000 / 587071136849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1271_neg : (321131571 / 1000000000) ≤ -Real.log (500000000000 / 689343482397) ∧
    -Real.log (500000000000 / 689343482397) ≤ (80282893 / 250000000) := by
  have h := checkLog_sound (w := (189343482397 / 1189343482397)) (n := 12)
    (lo := (321131571 / 1000000000)) (hi := (80282893 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((689343482397 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(689343482397 / 500000000000) = 1/(500000000000 / 689343482397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1271 : Bounds (321131571 / 1000000000) (80282893 / 250000000) (Real.log (689343482397 / 500000000000)) := by
  have h := reflection_log_1271_neg
  have he : Real.log (689343482397 / 500000000000) = -Real.log (500000000000 / 689343482397) := by
    rw [show ((689343482397 / 500000000000) : ℝ) = ((500000000000 / 689343482397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1272_neg : (12853471 / 40000000) ≤ -Real.log (62500000000 / 86185619127) ∧
    -Real.log (62500000000 / 86185619127) ≤ (40167097 / 125000000) := by
  have h := checkLog_sound (w := (23685619127 / 148685619127)) (n := 12)
    (lo := (12853471 / 40000000)) (hi := (40167097 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86185619127 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86185619127 / 62500000000) = 1/(62500000000 / 86185619127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1272 : Bounds (12853471 / 40000000) (40167097 / 125000000) (Real.log (86185619127 / 62500000000)) := by
  have h := reflection_log_1272_neg
  have he : Real.log (86185619127 / 62500000000) = -Real.log (62500000000 / 86185619127) := by
    rw [show ((86185619127 / 62500000000) : ℝ) = ((62500000000 / 86185619127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1273_neg : (147902629 / 1000000000) ≤ -Real.log (5000 / 5797) ∧
    -Real.log (5000 / 5797) ≤ (14790263 / 100000000) := by
  have h := checkLog_sound (w := (797 / 10797)) (n := 12)
    (lo := (147902629 / 1000000000)) (hi := (14790263 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5797 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5797 / 5000) = 1/(5000 / 5797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1273 : Bounds (147902629 / 1000000000) (14790263 / 100000000) (Real.log (5797 / 5000)) := by
  have h := reflection_log_1273_neg
  have he : Real.log (5797 / 5000) = -Real.log (5000 / 5797) := by
    rw [show ((5797 / 5000) : ℝ) = ((5000 / 5797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1274_neg : (43409839 / 250000000) ≤ -Real.log (4203 / 5000) ∧
    -Real.log (4203 / 5000) ≤ (173639357 / 1000000000) := by
  have h := checkLog_sound (w := (797 / 9203)) (n := 12)
    (lo := (43409839 / 250000000)) (hi := (173639357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4203) = 1/(4203 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1274 : Bounds (-173639357 / 1000000000) (-43409839 / 250000000) (Real.log (4203 / 5000)) := by
  have h := reflection_log_1274_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1275_neg : (159387 / 1000000000) ≤ -Real.log (5000000 / 5000797) ∧
    -Real.log (5000000 / 5000797) ≤ (39847 / 250000000) := by
  have h := checkLog_sound (w := (797 / 10000797)) (n := 12)
    (lo := (159387 / 1000000000)) (hi := (39847 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000797 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000797 / 5000000) = 1/(5000000 / 5000797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1275 : Bounds (159387 / 1000000000) (39847 / 250000000) (Real.log (5000797 / 5000000)) := by
  have h := reflection_log_1275_neg
  have he : Real.log (5000797 / 5000000) = -Real.log (5000000 / 5000797) := by
    rw [show ((5000797 / 5000000) : ℝ) = ((5000000 / 5000797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1276_neg : (39853 / 250000000) ≤ -Real.log (4999203 / 5000000) ∧
    -Real.log (4999203 / 5000000) ≤ (159413 / 1000000000) := by
  have h := checkLog_sound (w := (797 / 9999203)) (n := 12)
    (lo := (39853 / 250000000)) (hi := (159413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999203) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999203) = 1/(4999203 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1276 : Bounds (-159413 / 1000000000) (-39853 / 250000000) (Real.log (4999203 / 5000000)) := by
  have h := reflection_log_1276_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1277_neg : (38451353 / 500000000) ≤ -Real.log (1000000 / 1079937) ∧
    -Real.log (1000000 / 1079937) ≤ (76902707 / 1000000000) := by
  have h := checkLog_sound (w := (79937 / 2079937)) (n := 12)
    (lo := (38451353 / 500000000)) (hi := (76902707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1079937 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1079937 / 1000000) = 1/(1000000 / 1079937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1277 : Bounds (38451353 / 500000000) (76902707 / 1000000000) (Real.log (1079937 / 1000000)) := by
  have h := reflection_log_1277_neg
  have he : Real.log (1079937 / 1000000) = -Real.log (1000000 / 1079937) := by
    rw [show ((1079937 / 1000000) : ℝ) = ((1000000 / 1079937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1278_neg : (83313133 / 1000000000) ≤ -Real.log (920063 / 1000000) ∧
    -Real.log (920063 / 1000000) ≤ (41656567 / 500000000) := by
  have h := checkLog_sound (w := (79937 / 1920063)) (n := 12)
    (lo := (83313133 / 1000000000)) (hi := (41656567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 920063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 920063) = 1/(920063 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1278 : Bounds (-41656567 / 500000000) (-83313133 / 1000000000) (Real.log (920063 / 1000000)) := by
  have h := reflection_log_1278_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1279_neg : (19274517 / 250000000) ≤ -Real.log (250000 / 270037) ∧
    -Real.log (250000 / 270037) ≤ (77098069 / 1000000000) := by
  have h := checkLog_sound (w := (20037 / 520037)) (n := 12)
    (lo := (19274517 / 250000000)) (hi := (77098069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270037 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270037 / 250000) = 1/(250000 / 270037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1279 : Bounds (19274517 / 250000000) (77098069 / 1000000000) (Real.log (270037 / 250000)) := by
  have h := reflection_log_1279_neg
  have he : Real.log (270037 / 250000) = -Real.log (250000 / 270037) := by
    rw [show ((270037 / 250000) : ℝ) = ((250000 / 270037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
