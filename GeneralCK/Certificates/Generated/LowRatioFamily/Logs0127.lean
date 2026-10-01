import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8128_neg : (122775197 / 500000000) ≤ -Real.log (25000000000 / 31958117557) ∧
    -Real.log (25000000000 / 31958117557) ≤ (49110079 / 200000000) := by
  have h := checkLog_sound (w := (6958117557 / 56958117557)) (n := 12)
    (lo := (122775197 / 500000000)) (hi := (49110079 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31958117557 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31958117557 / 25000000000) = 1/(25000000000 / 31958117557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8128 : Bounds (122775197 / 500000000) (49110079 / 200000000) (Real.log (31958117557 / 25000000000)) := by
  have h := reflection_log_8128_neg
  have he : Real.log (31958117557 / 25000000000) = -Real.log (25000000000 / 31958117557) := by
    rw [show ((31958117557 / 25000000000) : ℝ) = ((25000000000 / 31958117557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8129_neg : (491671007 / 1000000000) ≤ -Real.log (500000000000 / 817523056653) ∧
    -Real.log (500000000000 / 817523056653) ≤ (15364719 / 31250000) := by
  have h := checkLog_sound (w := (317523056653 / 1317523056653)) (n := 12)
    (lo := (491671007 / 1000000000)) (hi := (15364719 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((817523056653 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(817523056653 / 500000000000) = 1/(500000000000 / 817523056653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8129 : Bounds (491671007 / 1000000000) (15364719 / 31250000) (Real.log (817523056653 / 500000000000)) := by
  have h := reflection_log_8129_neg
  have he : Real.log (817523056653 / 500000000000) = -Real.log (500000000000 / 817523056653) := by
    rw [show ((817523056653 / 500000000000) : ℝ) = ((500000000000 / 817523056653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8130_neg : (246366403 / 500000000) ≤ -Real.log (100000000000 / 163678312459) ∧
    -Real.log (100000000000 / 163678312459) ≤ (492732807 / 1000000000) := by
  have h := checkLog_sound (w := (63678312459 / 263678312459)) (n := 12)
    (lo := (246366403 / 500000000)) (hi := (492732807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163678312459 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163678312459 / 100000000000) = 1/(100000000000 / 163678312459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8130 : Bounds (246366403 / 500000000) (492732807 / 1000000000) (Real.log (163678312459 / 100000000000)) := by
  have h := reflection_log_8130_neg
  have he : Real.log (163678312459 / 100000000000) = -Real.log (100000000000 / 163678312459) := by
    rw [show ((163678312459 / 100000000000) : ℝ) = ((100000000000 / 163678312459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8131_neg : (216722983 / 1000000000) ≤ -Real.log (500 / 621) ∧
    -Real.log (500 / 621) ≤ (27090373 / 125000000) := by
  have h := checkLog_sound (w := (121 / 1121)) (n := 12)
    (lo := (216722983 / 1000000000)) (hi := (27090373 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(621 / 500) = 1/(500 / 621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8131 : Bounds (216722983 / 1000000000) (27090373 / 125000000) (Real.log (621 / 500)) := by
  have h := reflection_log_8131_neg
  have he : Real.log (621 / 500) = -Real.log (500 / 621) := by
    rw [show ((621 / 500) : ℝ) = ((500 / 621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8132_neg : (277071893 / 1000000000) ≤ -Real.log (379 / 500) ∧
    -Real.log (379 / 500) ≤ (138535947 / 500000000) := by
  have h := checkLog_sound (w := (121 / 879)) (n := 12)
    (lo := (277071893 / 1000000000)) (hi := (138535947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 379) = 1/(379 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8132 : Bounds (-138535947 / 500000000) (-277071893 / 1000000000) (Real.log (379 / 500)) := by
  have h := reflection_log_8132_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8133_neg : (24197 / 100000000) ≤ -Real.log (500000 / 500121) ∧
    -Real.log (500000 / 500121) ≤ (241971 / 1000000000) := by
  have h := checkLog_sound (w := (121 / 1000121)) (n := 12)
    (lo := (24197 / 100000000)) (hi := (241971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500121 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500121 / 500000) = 1/(500000 / 500121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8133 : Bounds (24197 / 100000000) (241971 / 1000000000) (Real.log (500121 / 500000)) := by
  have h := reflection_log_8133_neg
  have he : Real.log (500121 / 500000) = -Real.log (500000 / 500121) := by
    rw [show ((500121 / 500000) : ℝ) = ((500000 / 500121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8134_neg : (242029 / 1000000000) ≤ -Real.log (499879 / 500000) ∧
    -Real.log (499879 / 500000) ≤ (24203 / 100000000) := by
  have h := checkLog_sound (w := (121 / 999879)) (n := 12)
    (lo := (242029 / 1000000000)) (hi := (24203 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499879) = 1/(499879 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8134 : Bounds (-24203 / 100000000) (-242029 / 1000000000) (Real.log (499879 / 500000)) := by
  have h := reflection_log_8134_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8135_neg : (23008657 / 200000000) ≤ -Real.log (500000 / 560961) ∧
    -Real.log (500000 / 560961) ≤ (57521643 / 500000000) := by
  have h := checkLog_sound (w := (60961 / 1060961)) (n := 12)
    (lo := (23008657 / 200000000)) (hi := (57521643 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((560961 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(560961 / 500000) = 1/(500000 / 560961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8135 : Bounds (23008657 / 200000000) (57521643 / 500000000) (Real.log (560961 / 500000)) := by
  have h := reflection_log_8135_neg
  have he : Real.log (560961 / 500000) = -Real.log (500000 / 560961) := by
    rw [show ((560961 / 500000) : ℝ) = ((500000 / 560961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8136_neg : (130019851 / 1000000000) ≤ -Real.log (439039 / 500000) ∧
    -Real.log (439039 / 500000) ≤ (32504963 / 250000000) := by
  have h := checkLog_sound (w := (60961 / 939039)) (n := 12)
    (lo := (130019851 / 1000000000)) (hi := (32504963 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 439039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 439039) = 1/(439039 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8136 : Bounds (-32504963 / 250000000) (-130019851 / 1000000000) (Real.log (439039 / 500000)) := by
  have h := reflection_log_8136_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8137_neg : (28871767 / 250000000) ≤ -Real.log (50000 / 56121) ∧
    -Real.log (50000 / 56121) ≤ (115487069 / 1000000000) := by
  have h := checkLog_sound (w := (6121 / 106121)) (n := 12)
    (lo := (28871767 / 250000000)) (hi := (115487069 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56121 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(56121 / 50000) = 1/(50000 / 56121) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8137 : Bounds (28871767 / 250000000) (115487069 / 1000000000) (Real.log (56121 / 50000)) := by
  have h := reflection_log_8137_neg
  have he : Real.log (56121 / 50000) = -Real.log (50000 / 56121) := by
    rw [show ((56121 / 50000) : ℝ) = ((50000 / 56121) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8138_neg : (130587159 / 1000000000) ≤ -Real.log (43879 / 50000) ∧
    -Real.log (43879 / 50000) ≤ (3264679 / 25000000) := by
  have h := checkLog_sound (w := (6121 / 93879)) (n := 12)
    (lo := (130587159 / 1000000000)) (hi := (3264679 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 43879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 43879) = 1/(43879 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8138 : Bounds (-3264679 / 25000000) (-130587159 / 1000000000) (Real.log (43879 / 50000)) := by
  have h := reflection_log_8138_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8139_neg : (15100091 / 1000000000) ≤ -Real.log (2462533359 / 2500000000) ∧
    -Real.log (2462533359 / 2500000000) ≤ (3775023 / 250000000) := by
  have h := checkLog_sound (w := (37466641 / 4962533359)) (n := 12)
    (lo := (15100091 / 1000000000)) (hi := (3775023 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2462533359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2462533359) = 1/(2462533359 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8139 : Bounds (-3775023 / 250000000) (-15100091 / 1000000000) (Real.log (2462533359 / 2500000000)) := by
  have h := reflection_log_8139_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8140_neg : (2995313 / 200000000) ≤ -Real.log (246283756479 / 250000000000) ∧
    -Real.log (246283756479 / 250000000000) ≤ (7488283 / 500000000) := by
  have h := checkLog_sound (w := (3716243521 / 496283756479)) (n := 12)
    (lo := (2995313 / 200000000)) (hi := (7488283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246283756479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246283756479) = 1/(246283756479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8140 : Bounds (-7488283 / 500000000) (-2995313 / 200000000) (Real.log (246283756479 / 250000000000)) := by
  have h := reflection_log_8140_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8141_neg : (7658223 / 31250000) ≤ -Real.log (250000000000 / 319425495229) ∧
    -Real.log (250000000000 / 319425495229) ≤ (245063137 / 1000000000) := by
  have h := checkLog_sound (w := (69425495229 / 569425495229)) (n := 12)
    (lo := (7658223 / 31250000)) (hi := (245063137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((319425495229 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(319425495229 / 250000000000) = 1/(250000000000 / 319425495229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8141 : Bounds (7658223 / 31250000) (245063137 / 1000000000) (Real.log (319425495229 / 250000000000)) := by
  have h := reflection_log_8141_neg
  have he : Real.log (319425495229 / 250000000000) = -Real.log (250000000000 / 319425495229) := by
    rw [show ((319425495229 / 250000000000) : ℝ) = ((250000000000 / 319425495229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8142_neg : (61518557 / 250000000) ≤ -Real.log (125000000000 / 159874313453) ∧
    -Real.log (125000000000 / 159874313453) ≤ (246074229 / 1000000000) := by
  have h := checkLog_sound (w := (34874313453 / 284874313453)) (n := 12)
    (lo := (61518557 / 250000000)) (hi := (246074229 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159874313453 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159874313453 / 125000000000) = 1/(125000000000 / 159874313453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8142 : Bounds (61518557 / 250000000) (246074229 / 1000000000) (Real.log (159874313453 / 125000000000)) := by
  have h := reflection_log_8142_neg
  have he : Real.log (159874313453 / 125000000000) = -Real.log (125000000000 / 159874313453) := by
    rw [show ((159874313453 / 125000000000) : ℝ) = ((125000000000 / 159874313453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8143_neg : (246366403 / 500000000) ≤ -Real.log (250000000000 / 409195781147) ∧
    -Real.log (250000000000 / 409195781147) ≤ (492732807 / 1000000000) := by
  have h := checkLog_sound (w := (159195781147 / 659195781147)) (n := 12)
    (lo := (246366403 / 500000000)) (hi := (492732807 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((409195781147 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(409195781147 / 250000000000) = 1/(250000000000 / 409195781147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8143 : Bounds (246366403 / 500000000) (492732807 / 1000000000) (Real.log (409195781147 / 250000000000)) := by
  have h := reflection_log_8143_neg
  have he : Real.log (409195781147 / 250000000000) = -Real.log (250000000000 / 409195781147) := by
    rw [show ((409195781147 / 250000000000) : ℝ) = ((250000000000 / 409195781147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8144_neg : (123448719 / 250000000) ≤ -Real.log (500000000000 / 819261213721) ∧
    -Real.log (500000000000 / 819261213721) ≤ (493794877 / 1000000000) := by
  have h := checkLog_sound (w := (319261213721 / 1319261213721)) (n := 12)
    (lo := (123448719 / 250000000)) (hi := (493794877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819261213721 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819261213721 / 500000000000) = 1/(500000000000 / 819261213721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8144 : Bounds (123448719 / 250000000) (493794877 / 1000000000) (Real.log (819261213721 / 500000000000)) := by
  have h := reflection_log_8144_neg
  have he : Real.log (819261213721 / 500000000000) = -Real.log (500000000000 / 819261213721) := by
    rw [show ((819261213721 / 500000000000) : ℝ) = ((500000000000 / 819261213721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8145_neg : (108562739 / 500000000) ≤ -Real.log (400 / 497) ∧
    -Real.log (400 / 497) ≤ (217125479 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 897)) (n := 12)
    (lo := (108562739 / 500000000)) (hi := (217125479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((497 / 400) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(497 / 400) = 1/(400 / 497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8145 : Bounds (108562739 / 500000000) (217125479 / 1000000000) (Real.log (497 / 400)) := by
  have h := reflection_log_8145_neg
  have he : Real.log (497 / 400) = -Real.log (400 / 497) := by
    rw [show ((497 / 400) : ℝ) = ((400 / 497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8146_neg : (277731741 / 1000000000) ≤ -Real.log (303 / 400) ∧
    -Real.log (303 / 400) ≤ (138865871 / 500000000) := by
  have h := checkLog_sound (w := (97 / 703)) (n := 12)
    (lo := (277731741 / 1000000000)) (hi := (138865871 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400 / 303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400 / 303) = 1/(303 / 400) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8146 : Bounds (-138865871 / 500000000) (-277731741 / 1000000000) (Real.log (303 / 400)) := by
  have h := reflection_log_8146_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8147_neg : (24247 / 100000000) ≤ -Real.log (400000 / 400097) ∧
    -Real.log (400000 / 400097) ≤ (242471 / 1000000000) := by
  have h := checkLog_sound (w := (97 / 800097)) (n := 12)
    (lo := (24247 / 100000000)) (hi := (242471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400097 / 400000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400097 / 400000) = 1/(400000 / 400097) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8147 : Bounds (24247 / 100000000) (242471 / 1000000000) (Real.log (400097 / 400000)) := by
  have h := reflection_log_8147_neg
  have he : Real.log (400097 / 400000) = -Real.log (400000 / 400097) := by
    rw [show ((400097 / 400000) : ℝ) = ((400000 / 400097) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8148_neg : (242529 / 1000000000) ≤ -Real.log (399903 / 400000) ∧
    -Real.log (399903 / 400000) ≤ (24253 / 100000000) := by
  have h := checkLog_sound (w := (97 / 799903)) (n := 12)
    (lo := (242529 / 1000000000)) (hi := (24253 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000 / 399903) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000 / 399903) = 1/(399903 / 400000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8148 : Bounds (-24253 / 100000000) (-242529 / 1000000000) (Real.log (399903 / 400000)) := by
  have h := reflection_log_8148_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8149_neg : (57636611 / 500000000) ≤ -Real.log (50000 / 56109) ∧
    -Real.log (50000 / 56109) ≤ (115273223 / 1000000000) := by
  have h := checkLog_sound (w := (6109 / 106109)) (n := 12)
    (lo := (57636611 / 500000000)) (hi := (115273223 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((56109 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(56109 / 50000) = 1/(50000 / 56109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8149 : Bounds (57636611 / 500000000) (115273223 / 1000000000) (Real.log (56109 / 50000)) := by
  have h := reflection_log_8149_neg
  have he : Real.log (56109 / 50000) = -Real.log (50000 / 56109) := by
    rw [show ((56109 / 50000) : ℝ) = ((50000 / 56109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8150_neg : (130313717 / 1000000000) ≤ -Real.log (43891 / 50000) ∧
    -Real.log (43891 / 50000) ≤ (65156859 / 500000000) := by
  have h := checkLog_sound (w := (6109 / 93891)) (n := 12)
    (lo := (130313717 / 1000000000)) (hi := (65156859 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 43891) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 43891) = 1/(43891 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8150 : Bounds (-65156859 / 500000000) (-130313717 / 1000000000) (Real.log (43891 / 50000)) := by
  have h := reflection_log_8150_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8151_neg : (115717793 / 1000000000) ≤ -Real.log (1000000 / 1122679) ∧
    -Real.log (1000000 / 1122679) ≤ (57858897 / 500000000) := by
  have h := checkLog_sound (w := (122679 / 2122679)) (n := 12)
    (lo := (115717793 / 1000000000)) (hi := (57858897 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1122679 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1122679 / 1000000) = 1/(1000000 / 1122679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8151 : Bounds (115717793 / 1000000000) (57858897 / 500000000) (Real.log (1122679 / 1000000)) := by
  have h := reflection_log_8151_neg
  have he : Real.log (1122679 / 1000000) = -Real.log (1000000 / 1122679) := by
    rw [show ((1122679 / 1000000) : ℝ) = ((1000000 / 1122679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8152_neg : (130882333 / 1000000000) ≤ -Real.log (877321 / 1000000) ∧
    -Real.log (877321 / 1000000) ≤ (65441167 / 500000000) := by
  have h := checkLog_sound (w := (122679 / 1877321)) (n := 12)
    (lo := (130882333 / 1000000000)) (hi := (65441167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 877321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 877321) = 1/(877321 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8152 : Bounds (-65441167 / 500000000) (-130882333 / 1000000000) (Real.log (877321 / 1000000)) := by
  have h := reflection_log_8152_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8153_neg : (15164539 / 1000000000) ≤ -Real.log (984949862959 / 1000000000000) ∧
    -Real.log (984949862959 / 1000000000000) ≤ (758227 / 50000000) := by
  have h := checkLog_sound (w := (15050137041 / 1984949862959)) (n := 12)
    (lo := (15164539 / 1000000000)) (hi := (758227 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984949862959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984949862959) = 1/(984949862959 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8153 : Bounds (-758227 / 50000000) (-15164539 / 1000000000) (Real.log (984949862959 / 1000000000000)) := by
  have h := reflection_log_8153_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8154_neg : (3008099 / 200000000) ≤ -Real.log (2462680119 / 2500000000) ∧
    -Real.log (2462680119 / 2500000000) ≤ (940031 / 62500000) := by
  have h := checkLog_sound (w := (37319881 / 4962680119)) (n := 12)
    (lo := (3008099 / 200000000)) (hi := (940031 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2462680119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2462680119) = 1/(2462680119 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8154 : Bounds (-940031 / 62500000) (-3008099 / 200000000) (Real.log (2462680119 / 2500000000)) := by
  have h := reflection_log_8154_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8155_neg : (245586939 / 1000000000) ≤ -Real.log (250000000000 / 319592855027) ∧
    -Real.log (250000000000 / 319592855027) ≤ (12279347 / 50000000) := by
  have h := checkLog_sound (w := (69592855027 / 569592855027)) (n := 12)
    (lo := (245586939 / 1000000000)) (hi := (12279347 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((319592855027 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(319592855027 / 250000000000) = 1/(250000000000 / 319592855027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8155 : Bounds (245586939 / 1000000000) (12279347 / 50000000) (Real.log (319592855027 / 250000000000)) := by
  have h := reflection_log_8155_neg
  have he : Real.log (319592855027 / 250000000000) = -Real.log (250000000000 / 319592855027) := by
    rw [show ((319592855027 / 250000000000) : ℝ) = ((250000000000 / 319592855027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8156_neg : (123300063 / 500000000) ≤ -Real.log (500000000000 / 639833652677) ∧
    -Real.log (500000000000 / 639833652677) ≤ (246600127 / 1000000000) := by
  have h := checkLog_sound (w := (139833652677 / 1139833652677)) (n := 12)
    (lo := (123300063 / 500000000)) (hi := (246600127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((639833652677 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(639833652677 / 500000000000) = 1/(500000000000 / 639833652677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8156 : Bounds (123300063 / 500000000) (246600127 / 1000000000) (Real.log (639833652677 / 500000000000)) := by
  have h := reflection_log_8156_neg
  have he : Real.log (639833652677 / 500000000000) = -Real.log (500000000000 / 639833652677) := by
    rw [show ((639833652677 / 500000000000) : ℝ) = ((500000000000 / 639833652677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8157_neg : (123448719 / 250000000) ≤ -Real.log (12500000000 / 20481530343) ∧
    -Real.log (12500000000 / 20481530343) ≤ (493794877 / 1000000000) := by
  have h := checkLog_sound (w := (7981530343 / 32981530343)) (n := 12)
    (lo := (123448719 / 250000000)) (hi := (493794877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20481530343 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20481530343 / 12500000000) = 1/(12500000000 / 20481530343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8157 : Bounds (123448719 / 250000000) (493794877 / 1000000000) (Real.log (20481530343 / 12500000000)) := by
  have h := reflection_log_8157_neg
  have he : Real.log (20481530343 / 12500000000) = -Real.log (12500000000 / 20481530343) := by
    rw [show ((20481530343 / 12500000000) : ℝ) = ((12500000000 / 20481530343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8158_neg : (24742861 / 50000000) ≤ -Real.log (250000000000 / 410066006601) ∧
    -Real.log (250000000000 / 410066006601) ≤ (494857221 / 1000000000) := by
  have h := checkLog_sound (w := (160066006601 / 660066006601)) (n := 12)
    (lo := (24742861 / 50000000)) (hi := (494857221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((410066006601 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(410066006601 / 250000000000) = 1/(250000000000 / 410066006601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8158 : Bounds (24742861 / 50000000) (494857221 / 1000000000) (Real.log (410066006601 / 250000000000)) := by
  have h := reflection_log_8158_neg
  have he : Real.log (410066006601 / 250000000000) = -Real.log (250000000000 / 410066006601) := by
    rw [show ((410066006601 / 250000000000) : ℝ) = ((250000000000 / 410066006601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8159_neg : (54381953 / 250000000) ≤ -Real.log (1000 / 1243) ∧
    -Real.log (1000 / 1243) ≤ (217527813 / 1000000000) := by
  have h := checkLog_sound (w := (243 / 2243)) (n := 12)
    (lo := (54381953 / 250000000)) (hi := (217527813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1243 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1243 / 1000) = 1/(1000 / 1243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8159 : Bounds (54381953 / 250000000) (217527813 / 1000000000) (Real.log (1243 / 1000)) := by
  have h := reflection_log_8159_neg
  have he : Real.log (1243 / 1000) = -Real.log (1000 / 1243) := by
    rw [show ((1243 / 1000) : ℝ) = ((1000 / 1243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8160_neg : (11135681 / 40000000) ≤ -Real.log (757 / 1000) ∧
    -Real.log (757 / 1000) ≤ (139196013 / 500000000) := by
  have h := checkLog_sound (w := (243 / 1757)) (n := 12)
    (lo := (11135681 / 40000000)) (hi := (139196013 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 757) = 1/(757 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8160 : Bounds (-139196013 / 500000000) (-11135681 / 40000000) (Real.log (757 / 1000)) := by
  have h := reflection_log_8160_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8161_neg : (24297 / 100000000) ≤ -Real.log (1000000 / 1000243) ∧
    -Real.log (1000000 / 1000243) ≤ (242971 / 1000000000) := by
  have h := checkLog_sound (w := (243 / 2000243)) (n := 12)
    (lo := (24297 / 100000000)) (hi := (242971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000243 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000243 / 1000000) = 1/(1000000 / 1000243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8161 : Bounds (24297 / 100000000) (242971 / 1000000000) (Real.log (1000243 / 1000000)) := by
  have h := reflection_log_8161_neg
  have he : Real.log (1000243 / 1000000) = -Real.log (1000000 / 1000243) := by
    rw [show ((1000243 / 1000000) : ℝ) = ((1000000 / 1000243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8162_neg : (243029 / 1000000000) ≤ -Real.log (999757 / 1000000) ∧
    -Real.log (999757 / 1000000) ≤ (24303 / 100000000) := by
  have h := checkLog_sound (w := (243 / 1999757)) (n := 12)
    (lo := (243029 / 1000000000)) (hi := (24303 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999757) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999757) = 1/(999757 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8162 : Bounds (-24303 / 100000000) (-243029 / 1000000000) (Real.log (999757 / 1000000)) := by
  have h := reflection_log_8162_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8163_neg : (23100621 / 200000000) ≤ -Real.log (500000 / 561219) ∧
    -Real.log (500000 / 561219) ≤ (57751553 / 500000000) := by
  have h := checkLog_sound (w := (61219 / 1061219)) (n := 12)
    (lo := (23100621 / 200000000)) (hi := (57751553 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((561219 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(561219 / 500000) = 1/(500000 / 561219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8163 : Bounds (23100621 / 200000000) (57751553 / 500000000) (Real.log (561219 / 500000)) := by
  have h := reflection_log_8163_neg
  have he : Real.log (561219 / 500000) = -Real.log (500000 / 561219) := by
    rw [show ((561219 / 500000) : ℝ) = ((500000 / 561219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8164_neg : (13060767 / 100000000) ≤ -Real.log (438781 / 500000) ∧
    -Real.log (438781 / 500000) ≤ (130607671 / 1000000000) := by
  have h := checkLog_sound (w := (61219 / 938781)) (n := 12)
    (lo := (13060767 / 100000000)) (hi := (130607671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 438781) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 438781) = 1/(438781 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8164 : Bounds (-130607671 / 1000000000) (-13060767 / 100000000) (Real.log (438781 / 500000)) := by
  have h := reflection_log_8164_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8165_neg : (57973787 / 500000000) ≤ -Real.log (1000000 / 1122937) ∧
    -Real.log (1000000 / 1122937) ≤ (4637903 / 40000000) := by
  have h := checkLog_sound (w := (122937 / 2122937)) (n := 12)
    (lo := (57973787 / 500000000)) (hi := (4637903 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1122937 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1122937 / 1000000) = 1/(1000000 / 1122937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8165 : Bounds (57973787 / 500000000) (4637903 / 40000000) (Real.log (1122937 / 1000000)) := by
  have h := reflection_log_8165_neg
  have he : Real.log (1122937 / 1000000) = -Real.log (1000000 / 1122937) := by
    rw [show ((1122937 / 1000000) : ℝ) = ((1000000 / 1122937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8166_neg : (131176453 / 1000000000) ≤ -Real.log (877063 / 1000000) ∧
    -Real.log (877063 / 1000000) ≤ (65588227 / 500000000) := by
  have h := checkLog_sound (w := (122937 / 1877063)) (n := 12)
    (lo := (131176453 / 1000000000)) (hi := (65588227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 877063) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 877063) = 1/(877063 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8166 : Bounds (-65588227 / 500000000) (-131176453 / 1000000000) (Real.log (877063 / 1000000)) := by
  have h := reflection_log_8166_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8167_neg : (7614439 / 500000000) ≤ -Real.log (984886494031 / 1000000000000) ∧
    -Real.log (984886494031 / 1000000000000) ≤ (15228879 / 1000000000) := by
  have h := checkLog_sound (w := (15113505969 / 1984886494031)) (n := 12)
    (lo := (7614439 / 500000000)) (hi := (15228879 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 984886494031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 984886494031) = 1/(984886494031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8167 : Bounds (-15228879 / 1000000000) (-7614439 / 500000000) (Real.log (984886494031 / 1000000000000)) := by
  have h := reflection_log_8167_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8168_neg : (3020913 / 200000000) ≤ -Real.log (246252234039 / 250000000000) ∧
    -Real.log (246252234039 / 250000000000) ≤ (7552283 / 500000000) := by
  have h := checkLog_sound (w := (3747765961 / 496252234039)) (n := 12)
    (lo := (3020913 / 200000000)) (hi := (7552283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246252234039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246252234039) = 1/(246252234039 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8168 : Bounds (-7552283 / 500000000) (-3020913 / 200000000) (Real.log (246252234039 / 250000000000)) := by
  have h := reflection_log_8168_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8169_neg : (30763847 / 125000000) ≤ -Real.log (250000000000 / 319760313231) ∧
    -Real.log (250000000000 / 319760313231) ≤ (246110777 / 1000000000) := by
  have h := checkLog_sound (w := (69760313231 / 569760313231)) (n := 12)
    (lo := (30763847 / 125000000)) (hi := (246110777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((319760313231 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(319760313231 / 250000000000) = 1/(250000000000 / 319760313231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8169 : Bounds (30763847 / 125000000) (246110777 / 1000000000) (Real.log (319760313231 / 250000000000)) := by
  have h := reflection_log_8169_neg
  have he : Real.log (319760313231 / 250000000000) = -Real.log (250000000000 / 319760313231) := by
    rw [show ((319760313231 / 250000000000) : ℝ) = ((250000000000 / 319760313231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8170_neg : (247124027 / 1000000000) ≤ -Real.log (125000000000 / 160042237559) ∧
    -Real.log (125000000000 / 160042237559) ≤ (61781007 / 250000000) := by
  have h := checkLog_sound (w := (35042237559 / 285042237559)) (n := 12)
    (lo := (247124027 / 1000000000)) (hi := (61781007 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160042237559 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160042237559 / 125000000000) = 1/(125000000000 / 160042237559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8170 : Bounds (247124027 / 1000000000) (61781007 / 250000000) (Real.log (160042237559 / 125000000000)) := by
  have h := reflection_log_8170_neg
  have he : Real.log (160042237559 / 125000000000) = -Real.log (125000000000 / 160042237559) := by
    rw [show ((160042237559 / 125000000000) : ℝ) = ((125000000000 / 160042237559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8171_neg : (24742861 / 50000000) ≤ -Real.log (500000000000 / 820132013201) ∧
    -Real.log (500000000000 / 820132013201) ≤ (494857221 / 1000000000) := by
  have h := checkLog_sound (w := (320132013201 / 1320132013201)) (n := 12)
    (lo := (24742861 / 50000000)) (hi := (494857221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((820132013201 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(820132013201 / 500000000000) = 1/(500000000000 / 820132013201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8171 : Bounds (24742861 / 50000000) (494857221 / 1000000000) (Real.log (820132013201 / 500000000000)) := by
  have h := reflection_log_8171_neg
  have he : Real.log (820132013201 / 500000000000) = -Real.log (500000000000 / 820132013201) := by
    rw [show ((820132013201 / 500000000000) : ℝ) = ((500000000000 / 820132013201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8172_neg : (247959919 / 500000000) ≤ -Real.log (125000000000 / 205250990753) ∧
    -Real.log (125000000000 / 205250990753) ≤ (495919839 / 1000000000) := by
  have h := checkLog_sound (w := (80250990753 / 330250990753)) (n := 12)
    (lo := (247959919 / 500000000)) (hi := (495919839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((205250990753 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(205250990753 / 125000000000) = 1/(125000000000 / 205250990753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8172 : Bounds (247959919 / 500000000) (495919839 / 1000000000) (Real.log (205250990753 / 125000000000)) := by
  have h := reflection_log_8172_neg
  have he : Real.log (205250990753 / 125000000000) = -Real.log (125000000000 / 205250990753) := by
    rw [show ((205250990753 / 125000000000) : ℝ) = ((125000000000 / 205250990753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8173_neg : (851289 / 3906250) ≤ -Real.log (2000 / 2487) ∧
    -Real.log (2000 / 2487) ≤ (43585997 / 200000000) := by
  have h := checkLog_sound (w := (487 / 4487)) (n := 12)
    (lo := (851289 / 3906250)) (hi := (43585997 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2487 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2487 / 2000) = 1/(2000 / 2487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8173 : Bounds (851289 / 3906250) (43585997 / 200000000) (Real.log (2487 / 2000)) := by
  have h := reflection_log_8173_neg
  have he : Real.log (2487 / 2000) = -Real.log (2000 / 2487) := by
    rw [show ((2487 / 2000) : ℝ) = ((2000 / 2487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8174_neg : (55810549 / 200000000) ≤ -Real.log (1513 / 2000) ∧
    -Real.log (1513 / 2000) ≤ (139526373 / 500000000) := by
  have h := checkLog_sound (w := (487 / 3513)) (n := 12)
    (lo := (55810549 / 200000000)) (hi := (139526373 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1513) = 1/(1513 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8174 : Bounds (-139526373 / 500000000) (-55810549 / 200000000) (Real.log (1513 / 2000)) := by
  have h := reflection_log_8174_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8175_neg : (24347 / 100000000) ≤ -Real.log (2000000 / 2000487) ∧
    -Real.log (2000000 / 2000487) ≤ (243471 / 1000000000) := by
  have h := checkLog_sound (w := (487 / 4000487)) (n := 12)
    (lo := (24347 / 100000000)) (hi := (243471 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000487 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000487 / 2000000) = 1/(2000000 / 2000487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8175 : Bounds (24347 / 100000000) (243471 / 1000000000) (Real.log (2000487 / 2000000)) := by
  have h := reflection_log_8175_neg
  have he : Real.log (2000487 / 2000000) = -Real.log (2000000 / 2000487) := by
    rw [show ((2000487 / 2000000) : ℝ) = ((2000000 / 2000487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8176_neg : (243529 / 1000000000) ≤ -Real.log (1999513 / 2000000) ∧
    -Real.log (1999513 / 2000000) ≤ (24353 / 100000000) := by
  have h := checkLog_sound (w := (487 / 3999513)) (n := 12)
    (lo := (243529 / 1000000000)) (hi := (24353 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999513) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999513) = 1/(1999513 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8176 : Bounds (-24353 / 100000000) (-243529 / 1000000000) (Real.log (1999513 / 2000000)) := by
  have h := reflection_log_8176_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8177_neg : (23146587 / 200000000) ≤ -Real.log (125000 / 140337) ∧
    -Real.log (125000 / 140337) ≤ (14466617 / 125000000) := by
  have h := checkLog_sound (w := (15337 / 265337)) (n := 12)
    (lo := (23146587 / 200000000)) (hi := (14466617 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140337 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140337 / 125000) = 1/(125000 / 140337) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8177 : Bounds (23146587 / 200000000) (14466617 / 125000000) (Real.log (140337 / 125000)) := by
  have h := reflection_log_8177_neg
  have he : Real.log (140337 / 125000) = -Real.log (125000 / 140337) := by
    rw [show ((140337 / 125000) : ℝ) = ((125000 / 140337) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8178_neg : (13090171 / 100000000) ≤ -Real.log (109663 / 125000) ∧
    -Real.log (109663 / 125000) ≤ (130901711 / 1000000000) := by
  have h := checkLog_sound (w := (15337 / 234663)) (n := 12)
    (lo := (13090171 / 100000000)) (hi := (130901711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 109663) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 109663) = 1/(109663 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8178 : Bounds (-130901711 / 1000000000) (-13090171 / 100000000) (Real.log (109663 / 125000)) := by
  have h := reflection_log_8178_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8179_neg : (116178193 / 1000000000) ≤ -Real.log (250000 / 280799) ∧
    -Real.log (250000 / 280799) ≤ (58089097 / 500000000) := by
  have h := checkLog_sound (w := (30799 / 530799)) (n := 12)
    (lo := (116178193 / 1000000000)) (hi := (58089097 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((280799 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(280799 / 250000) = 1/(250000 / 280799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8179 : Bounds (116178193 / 1000000000) (58089097 / 500000000) (Real.log (280799 / 250000)) := by
  have h := reflection_log_8179_neg
  have he : Real.log (280799 / 250000) = -Real.log (250000 / 280799) := by
    rw [show ((280799 / 250000) : ℝ) = ((250000 / 280799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8180_neg : (657359 / 5000000) ≤ -Real.log (219201 / 250000) ∧
    -Real.log (219201 / 250000) ≤ (131471801 / 1000000000) := by
  have h := checkLog_sound (w := (30799 / 469201)) (n := 12)
    (lo := (657359 / 5000000)) (hi := (131471801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 219201) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 219201) = 1/(219201 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8180 : Bounds (-131471801 / 1000000000) (-657359 / 5000000) (Real.log (219201 / 250000)) := by
  have h := reflection_log_8180_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8181_neg : (15293607 / 1000000000) ≤ -Real.log (61551421599 / 62500000000) ∧
    -Real.log (61551421599 / 62500000000) ≤ (1911701 / 125000000) := by
  have h := checkLog_sound (w := (948578401 / 124051421599)) (n := 12)
    (lo := (15293607 / 1000000000)) (hi := (1911701 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 61551421599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 61551421599) = 1/(61551421599 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8181 : Bounds (-1911701 / 125000000) (-15293607 / 1000000000) (Real.log (61551421599 / 62500000000)) := by
  have h := reflection_log_8181_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8182_neg : (7584387 / 500000000) ≤ -Real.log (15389776431 / 15625000000) ∧
    -Real.log (15389776431 / 15625000000) ≤ (606751 / 40000000) := by
  have h := checkLog_sound (w := (235223569 / 31014776431)) (n := 12)
    (lo := (7584387 / 500000000)) (hi := (606751 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15389776431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15389776431) = 1/(15389776431 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8182 : Bounds (-606751 / 40000000) (-7584387 / 500000000) (Real.log (15389776431 / 15625000000)) := by
  have h := reflection_log_8182_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8183_neg : (123317323 / 500000000) ≤ -Real.log (500000000000 / 639855739857) ∧
    -Real.log (500000000000 / 639855739857) ≤ (246634647 / 1000000000) := by
  have h := checkLog_sound (w := (139855739857 / 1139855739857)) (n := 12)
    (lo := (123317323 / 500000000)) (hi := (246634647 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((639855739857 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(639855739857 / 500000000000) = 1/(500000000000 / 639855739857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8183 : Bounds (123317323 / 500000000) (246634647 / 1000000000) (Real.log (639855739857 / 500000000000)) := by
  have h := reflection_log_8183_neg
  have he : Real.log (639855739857 / 500000000000) = -Real.log (500000000000 / 639855739857) := by
    rw [show ((639855739857 / 500000000000) : ℝ) = ((500000000000 / 639855739857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8184_neg : (247649993 / 1000000000) ≤ -Real.log (125000000000 / 160126436467) ∧
    -Real.log (125000000000 / 160126436467) ≤ (123824997 / 500000000) := by
  have h := checkLog_sound (w := (35126436467 / 285126436467)) (n := 12)
    (lo := (247649993 / 1000000000)) (hi := (123824997 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160126436467 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(160126436467 / 125000000000) = 1/(125000000000 / 160126436467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8184 : Bounds (247649993 / 1000000000) (123824997 / 500000000) (Real.log (160126436467 / 125000000000)) := by
  have h := reflection_log_8184_neg
  have he : Real.log (160126436467 / 125000000000) = -Real.log (125000000000 / 160126436467) := by
    rw [show ((160126436467 / 125000000000) : ℝ) = ((125000000000 / 160126436467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8185_neg : (247959919 / 500000000) ≤ -Real.log (500000000000 / 821003963011) ∧
    -Real.log (500000000000 / 821003963011) ≤ (495919839 / 1000000000) := by
  have h := checkLog_sound (w := (321003963011 / 1321003963011)) (n := 12)
    (lo := (247959919 / 500000000)) (hi := (495919839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821003963011 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(821003963011 / 500000000000) = 1/(500000000000 / 821003963011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8185 : Bounds (247959919 / 500000000) (495919839 / 1000000000) (Real.log (821003963011 / 500000000000)) := by
  have h := reflection_log_8185_neg
  have he : Real.log (821003963011 / 500000000000) = -Real.log (500000000000 / 821003963011) := by
    rw [show ((821003963011 / 500000000000) : ℝ) = ((500000000000 / 821003963011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8186_neg : (49698273 / 100000000) ≤ -Real.log (500000000000 / 821877065433) ∧
    -Real.log (500000000000 / 821877065433) ≤ (496982731 / 1000000000) := by
  have h := checkLog_sound (w := (321877065433 / 1321877065433)) (n := 12)
    (lo := (49698273 / 100000000)) (hi := (496982731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821877065433 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(821877065433 / 500000000000) = 1/(500000000000 / 821877065433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8186 : Bounds (49698273 / 100000000) (496982731 / 1000000000) (Real.log (821877065433 / 500000000000)) := by
  have h := reflection_log_8186_neg
  have he : Real.log (821877065433 / 500000000000) = -Real.log (500000000000 / 821877065433) := by
    rw [show ((821877065433 / 500000000000) : ℝ) = ((500000000000 / 821877065433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8187_neg : (109165997 / 500000000) ≤ -Real.log (250 / 311) ∧
    -Real.log (250 / 311) ≤ (43666399 / 200000000) := by
  have h := checkLog_sound (w := (61 / 561)) (n := 12)
    (lo := (109165997 / 500000000)) (hi := (43666399 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311 / 250) = 1/(250 / 311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8187 : Bounds (109165997 / 500000000) (43666399 / 200000000) (Real.log (311 / 250)) := by
  have h := reflection_log_8187_neg
  have he : Real.log (311 / 250) = -Real.log (250 / 311) := by
    rw [show ((311 / 250) : ℝ) = ((250 / 311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8188_neg : (139856951 / 500000000) ≤ -Real.log (189 / 250) ∧
    -Real.log (189 / 250) ≤ (279713903 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 439)) (n := 12)
    (lo := (139856951 / 500000000)) (hi := (279713903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 189) = 1/(189 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8188 : Bounds (-279713903 / 1000000000) (-139856951 / 500000000) (Real.log (189 / 250)) := by
  have h := reflection_log_8188_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8189_neg : (24397 / 100000000) ≤ -Real.log (250000 / 250061) ∧
    -Real.log (250000 / 250061) ≤ (243971 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 500061)) (n := 12)
    (lo := (24397 / 100000000)) (hi := (243971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250061 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250061 / 250000) = 1/(250000 / 250061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8189 : Bounds (24397 / 100000000) (243971 / 1000000000) (Real.log (250061 / 250000)) := by
  have h := reflection_log_8189_neg
  have he : Real.log (250061 / 250000) = -Real.log (250000 / 250061) := by
    rw [show ((250061 / 250000) : ℝ) = ((250000 / 250061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8190_neg : (244029 / 1000000000) ≤ -Real.log (249939 / 250000) ∧
    -Real.log (249939 / 250000) ≤ (24403 / 100000000) := by
  have h := checkLog_sound (w := (61 / 499939)) (n := 12)
    (lo := (244029 / 1000000000)) (hi := (24403 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249939) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249939) = 1/(249939 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8190 : Bounds (-24403 / 100000000) (-244029 / 1000000000) (Real.log (249939 / 250000)) := by
  have h := reflection_log_8190_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8191_neg : (115962713 / 1000000000) ≤ -Real.log (500000 / 561477) ∧
    -Real.log (500000 / 561477) ≤ (57981357 / 500000000) := by
  have h := checkLog_sound (w := (61477 / 1061477)) (n := 12)
    (lo := (115962713 / 1000000000)) (hi := (57981357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((561477 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(561477 / 500000) = 1/(500000 / 561477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8191 : Bounds (115962713 / 1000000000) (57981357 / 500000000) (Real.log (561477 / 500000)) := by
  have h := reflection_log_8191_neg
  have he : Real.log (561477 / 500000) = -Real.log (500000 / 561477) := by
    rw [show ((561477 / 500000) : ℝ) = ((500000 / 561477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
