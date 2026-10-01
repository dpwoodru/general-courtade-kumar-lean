import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_11264_neg : (106922053 / 250000000) ≤ -Real.log (20000000000 / 30674156307) ∧
    -Real.log (20000000000 / 30674156307) ≤ (427688213 / 1000000000) := by
  have h := checkLog_sound (w := (10674156307 / 50674156307)) (n := 12)
    (lo := (106922053 / 250000000)) (hi := (427688213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((30674156307 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(30674156307 / 20000000000) = 1/(20000000000 / 30674156307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11264 : Bounds (106922053 / 250000000) (427688213 / 1000000000) (Real.log (30674156307 / 20000000000)) := by
  have h := reflection_log_11264_neg
  have he : Real.log (30674156307 / 20000000000) = -Real.log (20000000000 / 30674156307) := by
    rw [show ((30674156307 / 20000000000) : ℝ) = ((20000000000 / 30674156307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11265_neg : (864020657 / 1000000000) ≤ -Real.log (500000000000 / 1186340640809) ∧
    -Real.log (500000000000 / 1186340640809) ≤ (864020659 / 1000000000) := by
  have h := checkLog_sound (w := (186340640809 / 2186340640809)) (n := 12)
    (lo := (170873477 / 1000000000)) (hi := (85436739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1186340640809 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1186340640809 / 1000000000000) = 1/(500000000000 / 1186340640809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11265 : Bounds (864020657 / 1000000000) (864020659 / 1000000000) (Real.log (1186340640809 / 500000000000)) := by
  have h := reflection_log_11265_neg
  have he : Real.log (1186340640809 / 500000000000) = -Real.log (500000000000 / 1186340640809) := by
    rw [show ((1186340640809 / 500000000000) : ℝ) = ((500000000000 / 1186340640809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11266_neg : (866418901 / 1000000000) ≤ -Real.log (50000000000 / 118918918919) ∧
    -Real.log (50000000000 / 118918918919) ≤ (866418903 / 1000000000) := by
  have h := checkLog_sound (w := (18918918919 / 218918918919)) (n := 12)
    (lo := (173271721 / 1000000000)) (hi := (86635861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118918918919 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(118918918919 / 100000000000) = 1/(50000000000 / 118918918919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11266 : Bounds (866418901 / 1000000000) (866418903 / 1000000000) (Real.log (118918918919 / 50000000000)) := by
  have h := reflection_log_11266_neg
  have he : Real.log (118918918919 / 50000000000) = -Real.log (50000000000 / 118918918919) := by
    rw [show ((118918918919 / 50000000000) : ℝ) = ((50000000000 / 118918918919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11267_neg : (42860029 / 125000000) ≤ -Real.log (1000 / 1409) ∧
    -Real.log (1000 / 1409) ≤ (342880233 / 1000000000) := by
  have h := checkLog_sound (w := (409 / 2409)) (n := 12)
    (lo := (42860029 / 125000000)) (hi := (342880233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1409 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1409 / 1000) = 1/(1000 / 1409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11267 : Bounds (42860029 / 125000000) (342880233 / 1000000000) (Real.log (1409 / 1000)) := by
  have h := reflection_log_11267_neg
  have he : Real.log (1409 / 1000) = -Real.log (1000 / 1409) := by
    rw [show ((1409 / 1000) : ℝ) = ((1000 / 1409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11268_neg : (525939261 / 1000000000) ≤ -Real.log (591 / 1000) ∧
    -Real.log (591 / 1000) ≤ (262969631 / 500000000) := by
  have h := checkLog_sound (w := (409 / 1591)) (n := 12)
    (lo := (525939261 / 1000000000)) (hi := (262969631 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 591) = 1/(591 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11268 : Bounds (-262969631 / 500000000) (-525939261 / 1000000000) (Real.log (591 / 1000)) := by
  have h := reflection_log_11268_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11269_neg : (102229 / 250000000) ≤ -Real.log (1000000 / 1000409) ∧
    -Real.log (1000000 / 1000409) ≤ (408917 / 1000000000) := by
  have h := checkLog_sound (w := (409 / 2000409)) (n := 12)
    (lo := (102229 / 250000000)) (hi := (408917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000409 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000409 / 1000000) = 1/(1000000 / 1000409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11269 : Bounds (102229 / 250000000) (408917 / 1000000000) (Real.log (1000409 / 1000000)) := by
  have h := reflection_log_11269_neg
  have he : Real.log (1000409 / 1000000) = -Real.log (1000000 / 1000409) := by
    rw [show ((1000409 / 1000000) : ℝ) = ((1000000 / 1000409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11270_neg : (409083 / 1000000000) ≤ -Real.log (999591 / 1000000) ∧
    -Real.log (999591 / 1000000) ≤ (102271 / 250000000) := by
  have h := checkLog_sound (w := (409 / 1999591)) (n := 12)
    (lo := (409083 / 1000000000)) (hi := (102271 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999591) = 1/(999591 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11270 : Bounds (-102271 / 250000000) (-409083 / 1000000000) (Real.log (999591 / 1000000)) := by
  have h := reflection_log_11270_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11271_neg : (190824471 / 1000000000) ≤ -Real.log (1000000 / 1210247) ∧
    -Real.log (1000000 / 1210247) ≤ (23853059 / 125000000) := by
  have h := checkLog_sound (w := (210247 / 2210247)) (n := 12)
    (lo := (190824471 / 1000000000)) (hi := (23853059 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1210247 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1210247 / 1000000) = 1/(1000000 / 1210247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11271 : Bounds (190824471 / 1000000000) (23853059 / 125000000) (Real.log (1210247 / 1000000)) := by
  have h := reflection_log_11271_neg
  have he : Real.log (1210247 / 1000000) = -Real.log (1000000 / 1210247) := by
    rw [show ((1210247 / 1000000) : ℝ) = ((1000000 / 1210247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11272_neg : (1475219 / 6250000) ≤ -Real.log (789753 / 1000000) ∧
    -Real.log (789753 / 1000000) ≤ (236035041 / 1000000000) := by
  have h := checkLog_sound (w := (210247 / 1789753)) (n := 12)
    (lo := (1475219 / 6250000)) (hi := (236035041 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 789753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 789753) = 1/(789753 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11272 : Bounds (-236035041 / 1000000000) (-1475219 / 6250000) (Real.log (789753 / 1000000)) := by
  have h := reflection_log_11272_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11273_neg : (2993841 / 15625000) ≤ -Real.log (1000000 / 1211193) ∧
    -Real.log (1000000 / 1211193) ≤ (7664233 / 40000000) := by
  have h := checkLog_sound (w := (211193 / 2211193)) (n := 12)
    (lo := (2993841 / 15625000)) (hi := (7664233 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1211193 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1211193 / 1000000) = 1/(1000000 / 1211193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11273 : Bounds (2993841 / 15625000) (7664233 / 40000000) (Real.log (1211193 / 1000000)) := by
  have h := reflection_log_11273_neg
  have he : Real.log (1211193 / 1000000) = -Real.log (1000000 / 1211193) := by
    rw [show ((1211193 / 1000000) : ℝ) = ((1000000 / 1211193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11274_neg : (237233601 / 1000000000) ≤ -Real.log (788807 / 1000000) ∧
    -Real.log (788807 / 1000000) ≤ (118616801 / 500000000) := by
  have h := checkLog_sound (w := (211193 / 1788807)) (n := 12)
    (lo := (237233601 / 1000000000)) (hi := (118616801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 788807) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 788807) = 1/(788807 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11274 : Bounds (-118616801 / 500000000) (-237233601 / 1000000000) (Real.log (788807 / 1000000)) := by
  have h := reflection_log_11274_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11275_neg : (45627777 / 1000000000) ≤ -Real.log (955397516751 / 1000000000000) ∧
    -Real.log (955397516751 / 1000000000000) ≤ (22813889 / 500000000) := by
  have h := checkLog_sound (w := (44602483249 / 1955397516751)) (n := 12)
    (lo := (45627777 / 1000000000)) (hi := (22813889 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 955397516751) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 955397516751) = 1/(955397516751 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11275 : Bounds (-22813889 / 500000000) (-45627777 / 1000000000) (Real.log (955397516751 / 1000000000000)) := by
  have h := reflection_log_11275_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11276_neg : (45210569 / 1000000000) ≤ -Real.log (955796198991 / 1000000000000) ∧
    -Real.log (955796198991 / 1000000000000) ≤ (4521057 / 100000000) := by
  have h := checkLog_sound (w := (44203801009 / 1955796198991)) (n := 12)
    (lo := (45210569 / 1000000000)) (hi := (4521057 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 955796198991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 955796198991) = 1/(955796198991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11276 : Bounds (-4521057 / 100000000) (-45210569 / 1000000000) (Real.log (955796198991 / 1000000000000)) := by
  have h := reflection_log_11276_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11277_neg : (426859511 / 1000000000) ≤ -Real.log (250000000000 / 383109339249) ∧
    -Real.log (250000000000 / 383109339249) ≤ (53357439 / 125000000) := by
  have h := checkLog_sound (w := (133109339249 / 633109339249)) (n := 12)
    (lo := (426859511 / 1000000000)) (hi := (53357439 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383109339249 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(383109339249 / 250000000000) = 1/(250000000000 / 383109339249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11277 : Bounds (426859511 / 1000000000) (53357439 / 125000000) (Real.log (383109339249 / 250000000000)) := by
  have h := reflection_log_11277_neg
  have he : Real.log (383109339249 / 250000000000) = -Real.log (250000000000 / 383109339249) := by
    rw [show ((383109339249 / 250000000000) : ℝ) = ((250000000000 / 383109339249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11278_neg : (17153577 / 40000000) ≤ -Real.log (500000000000 / 767737228499) ∧
    -Real.log (500000000000 / 767737228499) ≤ (214419713 / 500000000) := by
  have h := checkLog_sound (w := (267737228499 / 1267737228499)) (n := 12)
    (lo := (17153577 / 40000000)) (hi := (214419713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((767737228499 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(767737228499 / 500000000000) = 1/(500000000000 / 767737228499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11278 : Bounds (17153577 / 40000000) (214419713 / 500000000) (Real.log (767737228499 / 500000000000)) := by
  have h := reflection_log_11278_neg
  have he : Real.log (767737228499 / 500000000000) = -Real.log (500000000000 / 767737228499) := by
    rw [show ((767737228499 / 500000000000) : ℝ) = ((500000000000 / 767737228499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11279_neg : (866418901 / 1000000000) ≤ -Real.log (500000000000 / 1189189189189) ∧
    -Real.log (500000000000 / 1189189189189) ≤ (866418903 / 1000000000) := by
  have h := checkLog_sound (w := (189189189189 / 2189189189189)) (n := 12)
    (lo := (173271721 / 1000000000)) (hi := (86635861 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1189189189189 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1189189189189 / 1000000000000) = 1/(500000000000 / 1189189189189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11279 : Bounds (866418901 / 1000000000) (866418903 / 1000000000) (Real.log (1189189189189 / 500000000000)) := by
  have h := reflection_log_11279_neg
  have he : Real.log (1189189189189 / 500000000000) = -Real.log (500000000000 / 1189189189189) := by
    rw [show ((1189189189189 / 500000000000) : ℝ) = ((500000000000 / 1189189189189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11280_neg : (868819493 / 1000000000) ≤ -Real.log (500000000000 / 1192047377327) ∧
    -Real.log (500000000000 / 1192047377327) ≤ (173763899 / 200000000) := by
  have h := checkLog_sound (w := (192047377327 / 2192047377327)) (n := 12)
    (lo := (175672313 / 1000000000)) (hi := (87836157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1192047377327 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1192047377327 / 1000000000000) = 1/(500000000000 / 1192047377327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11280 : Bounds (868819493 / 1000000000) (173763899 / 200000000) (Real.log (1192047377327 / 500000000000)) := by
  have h := reflection_log_11280_neg
  have he : Real.log (1192047377327 / 500000000000) = -Real.log (500000000000 / 1192047377327) := by
    rw [show ((1192047377327 / 500000000000) : ℝ) = ((500000000000 / 1192047377327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11281_neg : (42948713 / 125000000) ≤ -Real.log (100 / 141) ∧
    -Real.log (100 / 141) ≤ (68717941 / 200000000) := by
  have h := checkLog_sound (w := (41 / 241)) (n := 12)
    (lo := (42948713 / 125000000)) (hi := (68717941 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((141 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(141 / 100) = 1/(100 / 141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11281 : Bounds (42948713 / 125000000) (68717941 / 200000000) (Real.log (141 / 100)) := by
  have h := reflection_log_11281_neg
  have he : Real.log (141 / 100) = -Real.log (100 / 141) := by
    rw [show ((141 / 100) : ℝ) = ((100 / 141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11282_neg : (263816371 / 500000000) ≤ -Real.log (59 / 100) ∧
    -Real.log (59 / 100) ≤ (527632743 / 1000000000) := by
  have h := checkLog_sound (w := (41 / 159)) (n := 12)
    (lo := (263816371 / 500000000)) (hi := (527632743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100 / 59) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100 / 59) = 1/(59 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11282 : Bounds (-527632743 / 1000000000) (-263816371 / 500000000) (Real.log (59 / 100)) := by
  have h := reflection_log_11282_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11283_neg : (81983 / 200000000) ≤ -Real.log (100000 / 100041) ∧
    -Real.log (100000 / 100041) ≤ (102479 / 250000000) := by
  have h := checkLog_sound (w := (41 / 200041)) (n := 12)
    (lo := (81983 / 200000000)) (hi := (102479 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100041 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100041 / 100000) = 1/(100000 / 100041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11283 : Bounds (81983 / 200000000) (102479 / 250000000) (Real.log (100041 / 100000)) := by
  have h := reflection_log_11283_neg
  have he : Real.log (100041 / 100000) = -Real.log (100000 / 100041) := by
    rw [show ((100041 / 100000) : ℝ) = ((100000 / 100041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11284_neg : (102521 / 250000000) ≤ -Real.log (99959 / 100000) ∧
    -Real.log (99959 / 100000) ≤ (82017 / 200000000) := by
  have h := checkLog_sound (w := (41 / 199959)) (n := 12)
    (lo := (102521 / 250000000)) (hi := (82017 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99959) = 1/(99959 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11284 : Bounds (-82017 / 200000000) (-102521 / 250000000) (Real.log (99959 / 100000)) := by
  have h := reflection_log_11284_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11285_neg : (95638997 / 500000000) ≤ -Real.log (250000 / 302699) ∧
    -Real.log (250000 / 302699) ≤ (38255599 / 200000000) := by
  have h := checkLog_sound (w := (52699 / 552699)) (n := 12)
    (lo := (95638997 / 500000000)) (hi := (38255599 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((302699 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(302699 / 250000) = 1/(250000 / 302699) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11285 : Bounds (95638997 / 500000000) (38255599 / 200000000) (Real.log (302699 / 250000)) := by
  have h := reflection_log_11285_neg
  have he : Real.log (302699 / 250000) = -Real.log (250000 / 302699) := by
    rw [show ((302699 / 250000) : ℝ) = ((250000 / 302699) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11286_neg : (59182609 / 250000000) ≤ -Real.log (197301 / 250000) ∧
    -Real.log (197301 / 250000) ≤ (236730437 / 1000000000) := by
  have h := checkLog_sound (w := (52699 / 447301)) (n := 12)
    (lo := (59182609 / 250000000)) (hi := (236730437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 197301) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 197301) = 1/(197301 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11286 : Bounds (-236730437 / 1000000000) (-59182609 / 250000000) (Real.log (197301 / 250000)) := by
  have h := reflection_log_11286_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11287_neg : (192058993 / 1000000000) ≤ -Real.log (500000 / 605871) ∧
    -Real.log (500000 / 605871) ≤ (96029497 / 500000000) := by
  have h := checkLog_sound (w := (105871 / 1105871)) (n := 12)
    (lo := (192058993 / 1000000000)) (hi := (96029497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((605871 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(605871 / 500000) = 1/(500000 / 605871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11287 : Bounds (192058993 / 1000000000) (96029497 / 500000000) (Real.log (605871 / 500000)) := by
  have h := reflection_log_11287_neg
  have he : Real.log (605871 / 500000) = -Real.log (500000 / 605871) := by
    rw [show ((605871 / 500000) : ℝ) = ((500000 / 605871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11288_neg : (237929831 / 1000000000) ≤ -Real.log (394129 / 500000) ∧
    -Real.log (394129 / 500000) ≤ (29741229 / 125000000) := by
  have h := checkLog_sound (w := (105871 / 894129)) (n := 12)
    (lo := (237929831 / 1000000000)) (hi := (29741229 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 394129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 394129) = 1/(394129 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11288 : Bounds (-29741229 / 125000000) (-237929831 / 1000000000) (Real.log (394129 / 500000)) := by
  have h := reflection_log_11288_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11289_neg : (45870837 / 1000000000) ≤ -Real.log (238791331359 / 250000000000) ∧
    -Real.log (238791331359 / 250000000000) ≤ (22935419 / 500000000) := by
  have h := checkLog_sound (w := (11208668641 / 488791331359)) (n := 12)
    (lo := (45870837 / 1000000000)) (hi := (22935419 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 238791331359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 238791331359) = 1/(238791331359 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11289 : Bounds (-22935419 / 500000000) (-45870837 / 1000000000) (Real.log (238791331359 / 250000000000)) := by
  have h := reflection_log_11289_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11290_neg : (45452441 / 1000000000) ≤ -Real.log (59722815399 / 62500000000) ∧
    -Real.log (59722815399 / 62500000000) ≤ (22726221 / 500000000) := by
  have h := checkLog_sound (w := (2777184601 / 122222815399)) (n := 12)
    (lo := (45452441 / 1000000000)) (hi := (22726221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 59722815399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 59722815399) = 1/(59722815399 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11290 : Bounds (-22726221 / 500000000) (-45452441 / 1000000000) (Real.log (59722815399 / 62500000000)) := by
  have h := reflection_log_11290_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11291_neg : (42800843 / 100000000) ≤ -Real.log (250000000000 / 383549753929) ∧
    -Real.log (250000000000 / 383549753929) ≤ (428008431 / 1000000000) := by
  have h := checkLog_sound (w := (133549753929 / 633549753929)) (n := 12)
    (lo := (42800843 / 100000000)) (hi := (428008431 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((383549753929 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(383549753929 / 250000000000) = 1/(250000000000 / 383549753929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11291 : Bounds (42800843 / 100000000) (428008431 / 1000000000) (Real.log (383549753929 / 250000000000)) := by
  have h := reflection_log_11291_neg
  have he : Real.log (383549753929 / 250000000000) = -Real.log (250000000000 / 383549753929) := by
    rw [show ((383549753929 / 250000000000) : ℝ) = ((250000000000 / 383549753929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11292_neg : (17199553 / 40000000) ≤ -Real.log (62500000000 / 96077521573) ∧
    -Real.log (62500000000 / 96077521573) ≤ (214994413 / 500000000) := by
  have h := checkLog_sound (w := (33577521573 / 158577521573)) (n := 12)
    (lo := (17199553 / 40000000)) (hi := (214994413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96077521573 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(96077521573 / 62500000000) = 1/(62500000000 / 96077521573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11292 : Bounds (17199553 / 40000000) (214994413 / 500000000) (Real.log (96077521573 / 62500000000)) := by
  have h := reflection_log_11292_neg
  have he : Real.log (96077521573 / 62500000000) = -Real.log (62500000000 / 96077521573) := by
    rw [show ((96077521573 / 62500000000) : ℝ) = ((62500000000 / 96077521573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11293_neg : (868819493 / 1000000000) ≤ -Real.log (250000000000 / 596023688663) ∧
    -Real.log (250000000000 / 596023688663) ≤ (173763899 / 200000000) := by
  have h := checkLog_sound (w := (96023688663 / 1096023688663)) (n := 12)
    (lo := (175672313 / 1000000000)) (hi := (87836157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596023688663 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(596023688663 / 500000000000) = 1/(250000000000 / 596023688663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11293 : Bounds (868819493 / 1000000000) (173763899 / 200000000) (Real.log (596023688663 / 250000000000)) := by
  have h := reflection_log_11293_neg
  have he : Real.log (596023688663 / 250000000000) = -Real.log (250000000000 / 596023688663) := by
    rw [show ((596023688663 / 250000000000) : ℝ) = ((250000000000 / 596023688663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11294_neg : (174244489 / 200000000) ≤ -Real.log (250000000000 / 597457627119) ∧
    -Real.log (250000000000 / 597457627119) ≤ (871222447 / 1000000000) := by
  have h := checkLog_sound (w := (97457627119 / 1097457627119)) (n := 12)
    (lo := (35615053 / 200000000)) (hi := (89037633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597457627119 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(597457627119 / 500000000000) = 1/(250000000000 / 597457627119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11294 : Bounds (174244489 / 200000000) (871222447 / 1000000000) (Real.log (597457627119 / 250000000000)) := by
  have h := reflection_log_11294_neg
  have he : Real.log (597457627119 / 250000000000) = -Real.log (250000000000 / 597457627119) := by
    rw [show ((597457627119 / 250000000000) : ℝ) = ((250000000000 / 597457627119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11295_neg : (21518667 / 62500000) ≤ -Real.log (1000 / 1411) ∧
    -Real.log (1000 / 1411) ≤ (344298673 / 1000000000) := by
  have h := checkLog_sound (w := (411 / 2411)) (n := 12)
    (lo := (21518667 / 62500000)) (hi := (344298673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1411 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1411 / 1000) = 1/(1000 / 1411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11295 : Bounds (21518667 / 62500000) (344298673 / 1000000000) (Real.log (1411 / 1000)) := by
  have h := reflection_log_11295_neg
  have he : Real.log (1411 / 1000) = -Real.log (1000 / 1411) := by
    rw [show ((1411 / 1000) : ℝ) = ((1000 / 1411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11296_neg : (105865819 / 200000000) ≤ -Real.log (589 / 1000) ∧
    -Real.log (589 / 1000) ≤ (66166137 / 125000000) := by
  have h := checkLog_sound (w := (411 / 1589)) (n := 12)
    (lo := (105865819 / 200000000)) (hi := (66166137 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 589) = 1/(589 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11296 : Bounds (-66166137 / 125000000) (-105865819 / 200000000) (Real.log (589 / 1000)) := by
  have h := reflection_log_11296_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11297_neg : (82183 / 200000000) ≤ -Real.log (1000000 / 1000411) ∧
    -Real.log (1000000 / 1000411) ≤ (102729 / 250000000) := by
  have h := checkLog_sound (w := (411 / 2000411)) (n := 12)
    (lo := (82183 / 200000000)) (hi := (102729 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000411 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000411 / 1000000) = 1/(1000000 / 1000411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11297 : Bounds (82183 / 200000000) (102729 / 250000000) (Real.log (1000411 / 1000000)) := by
  have h := reflection_log_11297_neg
  have he : Real.log (1000411 / 1000000) = -Real.log (1000000 / 1000411) := by
    rw [show ((1000411 / 1000000) : ℝ) = ((1000000 / 1000411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11298_neg : (102771 / 250000000) ≤ -Real.log (999589 / 1000000) ∧
    -Real.log (999589 / 1000000) ≤ (82217 / 200000000) := by
  have h := checkLog_sound (w := (411 / 1999589)) (n := 12)
    (lo := (102771 / 250000000)) (hi := (82217 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999589) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999589) = 1/(999589 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11298 : Bounds (-82217 / 200000000) (-102771 / 250000000) (Real.log (999589 / 1000000)) := by
  have h := reflection_log_11298_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11299_neg : (11983207 / 62500000) ≤ -Real.log (200000 / 242269) ∧
    -Real.log (200000 / 242269) ≤ (191731313 / 1000000000) := by
  have h := checkLog_sound (w := (42269 / 442269)) (n := 12)
    (lo := (11983207 / 62500000)) (hi := (191731313 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242269 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242269 / 200000) = 1/(200000 / 242269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11299 : Bounds (11983207 / 62500000) (191731313 / 1000000000) (Real.log (242269 / 200000)) := by
  have h := reflection_log_11299_neg
  have he : Real.log (242269 / 200000) = -Real.log (200000 / 242269) := by
    rw [show ((242269 / 200000) : ℝ) = ((200000 / 242269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11300_neg : (59356579 / 250000000) ≤ -Real.log (157731 / 200000) ∧
    -Real.log (157731 / 200000) ≤ (237426317 / 1000000000) := by
  have h := checkLog_sound (w := (42269 / 357731)) (n := 12)
    (lo := (59356579 / 250000000)) (hi := (237426317 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 157731) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 157731) = 1/(157731 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11300 : Bounds (-237426317 / 1000000000) (-59356579 / 250000000) (Real.log (157731 / 200000)) := by
  have h := reflection_log_11300_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11301_neg : (192513607 / 1000000000) ≤ -Real.log (1000000 / 1212293) ∧
    -Real.log (1000000 / 1212293) ≤ (24064201 / 125000000) := by
  have h := checkLog_sound (w := (212293 / 2212293)) (n := 12)
    (lo := (192513607 / 1000000000)) (hi := (24064201 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1212293 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1212293 / 1000000) = 1/(1000000 / 1212293) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11301 : Bounds (192513607 / 1000000000) (24064201 / 125000000) (Real.log (1212293 / 1000000)) := by
  have h := reflection_log_11301_neg
  have he : Real.log (1212293 / 1000000) = -Real.log (1000000 / 1212293) := by
    rw [show ((1212293 / 1000000) : ℝ) = ((1000000 / 1212293) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11302_neg : (47725817 / 200000000) ≤ -Real.log (787707 / 1000000) ∧
    -Real.log (787707 / 1000000) ≤ (119314543 / 500000000) := by
  have h := checkLog_sound (w := (212293 / 1787707)) (n := 12)
    (lo := (47725817 / 200000000)) (hi := (119314543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 787707) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 787707) = 1/(787707 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11302 : Bounds (-119314543 / 500000000) (-47725817 / 200000000) (Real.log (787707 / 1000000)) := by
  have h := reflection_log_11302_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11303_neg : (23057739 / 500000000) ≤ -Real.log (954931682151 / 1000000000000) ∧
    -Real.log (954931682151 / 1000000000000) ≤ (46115479 / 1000000000) := by
  have h := checkLog_sound (w := (45068317849 / 1954931682151)) (n := 12)
    (lo := (23057739 / 500000000)) (hi := (46115479 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 954931682151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 954931682151) = 1/(954931682151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11303 : Bounds (-46115479 / 1000000000) (-23057739 / 500000000) (Real.log (954931682151 / 1000000000000)) := by
  have h := reflection_log_11303_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11304_neg : (45695003 / 1000000000) ≤ -Real.log (38213331639 / 40000000000) ∧
    -Real.log (38213331639 / 40000000000) ≤ (11423751 / 250000000) := by
  have h := checkLog_sound (w := (1786668361 / 78213331639)) (n := 12)
    (lo := (45695003 / 1000000000)) (hi := (11423751 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38213331639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38213331639) = 1/(38213331639 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11304 : Bounds (-11423751 / 250000000) (-45695003 / 1000000000) (Real.log (38213331639 / 40000000000)) := by
  have h := reflection_log_11304_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11305_neg : (107289407 / 250000000) ≤ -Real.log (125000000000 / 191995390887) ∧
    -Real.log (125000000000 / 191995390887) ≤ (429157629 / 1000000000) := by
  have h := checkLog_sound (w := (66995390887 / 316995390887)) (n := 12)
    (lo := (107289407 / 250000000)) (hi := (429157629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((191995390887 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(191995390887 / 125000000000) = 1/(125000000000 / 191995390887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11305 : Bounds (107289407 / 250000000) (429157629 / 1000000000) (Real.log (191995390887 / 125000000000)) := by
  have h := reflection_log_11305_neg
  have he : Real.log (191995390887 / 125000000000) = -Real.log (125000000000 / 191995390887) := by
    rw [show ((191995390887 / 125000000000) : ℝ) = ((125000000000 / 191995390887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11306_neg : (431142693 / 1000000000) ≤ -Real.log (500000000000 / 769507570709) ∧
    -Real.log (500000000000 / 769507570709) ≤ (215571347 / 500000000) := by
  have h := checkLog_sound (w := (269507570709 / 1269507570709)) (n := 12)
    (lo := (431142693 / 1000000000)) (hi := (215571347 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((769507570709 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(769507570709 / 500000000000) = 1/(500000000000 / 769507570709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11306 : Bounds (431142693 / 1000000000) (215571347 / 500000000) (Real.log (769507570709 / 500000000000)) := by
  have h := reflection_log_11306_neg
  have he : Real.log (769507570709 / 500000000000) = -Real.log (500000000000 / 769507570709) := by
    rw [show ((769507570709 / 500000000000) : ℝ) = ((500000000000 / 769507570709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11307_neg : (174244489 / 200000000) ≤ -Real.log (500000000000 / 1194915254237) ∧
    -Real.log (500000000000 / 1194915254237) ≤ (871222447 / 1000000000) := by
  have h := checkLog_sound (w := (194915254237 / 2194915254237)) (n := 12)
    (lo := (35615053 / 200000000)) (hi := (89037633 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1194915254237 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1194915254237 / 1000000000000) = 1/(500000000000 / 1194915254237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11307 : Bounds (174244489 / 200000000) (871222447 / 1000000000) (Real.log (1194915254237 / 500000000000)) := by
  have h := reflection_log_11307_neg
  have he : Real.log (1194915254237 / 500000000000) = -Real.log (500000000000 / 1194915254237) := by
    rw [show ((1194915254237 / 500000000000) : ℝ) = ((500000000000 / 1194915254237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11308_neg : (873627767 / 1000000000) ≤ -Real.log (50000000000 / 119779286927) ∧
    -Real.log (50000000000 / 119779286927) ≤ (873627769 / 1000000000) := by
  have h := checkLog_sound (w := (19779286927 / 219779286927)) (n := 12)
    (lo := (180480587 / 1000000000)) (hi := (45120147 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119779286927 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(119779286927 / 100000000000) = 1/(50000000000 / 119779286927) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11308 : Bounds (873627767 / 1000000000) (873627769 / 1000000000) (Real.log (119779286927 / 50000000000)) := by
  have h := reflection_log_11308_neg
  have he : Real.log (119779286927 / 50000000000) = -Real.log (50000000000 / 119779286927) := by
    rw [show ((119779286927 / 50000000000) : ℝ) = ((50000000000 / 119779286927) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11309_neg : (345007139 / 1000000000) ≤ -Real.log (250 / 353) ∧
    -Real.log (250 / 353) ≤ (17250357 / 50000000) := by
  have h := checkLog_sound (w := (103 / 603)) (n := 12)
    (lo := (345007139 / 1000000000)) (hi := (17250357 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((353 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(353 / 250) = 1/(250 / 353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11309 : Bounds (345007139 / 1000000000) (17250357 / 50000000) (Real.log (353 / 250)) := by
  have h := reflection_log_11309_neg
  have he : Real.log (353 / 250) = -Real.log (250 / 353) := by
    rw [show ((353 / 250) : ℝ) = ((250 / 353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11310_neg : (531028331 / 1000000000) ≤ -Real.log (147 / 250) ∧
    -Real.log (147 / 250) ≤ (132757083 / 250000000) := by
  have h := checkLog_sound (w := (103 / 397)) (n := 12)
    (lo := (531028331 / 1000000000)) (hi := (132757083 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 147) = 1/(147 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11310 : Bounds (-132757083 / 250000000) (-531028331 / 1000000000) (Real.log (147 / 250)) := by
  have h := reflection_log_11310_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11311_neg : (82383 / 200000000) ≤ -Real.log (250000 / 250103) ∧
    -Real.log (250000 / 250103) ≤ (102979 / 250000000) := by
  have h := checkLog_sound (w := (103 / 500103)) (n := 12)
    (lo := (82383 / 200000000)) (hi := (102979 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250103 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250103 / 250000) = 1/(250000 / 250103) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11311 : Bounds (82383 / 200000000) (102979 / 250000000) (Real.log (250103 / 250000)) := by
  have h := reflection_log_11311_neg
  have he : Real.log (250103 / 250000) = -Real.log (250000 / 250103) := by
    rw [show ((250103 / 250000) : ℝ) = ((250000 / 250103) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11312_neg : (103021 / 250000000) ≤ -Real.log (249897 / 250000) ∧
    -Real.log (249897 / 250000) ≤ (82417 / 200000000) := by
  have h := checkLog_sound (w := (103 / 499897)) (n := 12)
    (lo := (103021 / 250000000)) (hi := (82417 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249897) = 1/(249897 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11312 : Bounds (-82417 / 200000000) (-103021 / 250000000) (Real.log (249897 / 250000)) := by
  have h := reflection_log_11312_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11313_neg : (768741 / 4000000) ≤ -Real.log (200000 / 242379) ∧
    -Real.log (200000 / 242379) ≤ (192185251 / 1000000000) := by
  have h := checkLog_sound (w := (42379 / 442379)) (n := 12)
    (lo := (768741 / 4000000)) (hi := (192185251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((242379 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(242379 / 200000) = 1/(200000 / 242379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11313 : Bounds (768741 / 4000000) (192185251 / 1000000000) (Real.log (242379 / 200000)) := by
  have h := reflection_log_11313_neg
  have he : Real.log (242379 / 200000) = -Real.log (200000 / 242379) := by
    rw [show ((242379 / 200000) : ℝ) = ((200000 / 242379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11314_neg : (238123949 / 1000000000) ≤ -Real.log (157621 / 200000) ∧
    -Real.log (157621 / 200000) ≤ (4762479 / 20000000) := by
  have h := checkLog_sound (w := (42379 / 357621)) (n := 12)
    (lo := (238123949 / 1000000000)) (hi := (4762479 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 157621) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 157621) = 1/(157621 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11314 : Bounds (-4762479 / 20000000) (-238123949 / 1000000000) (Real.log (157621 / 200000)) := by
  have h := reflection_log_11314_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11315_neg : (19296719 / 100000000) ≤ -Real.log (1000000 / 1212843) ∧
    -Real.log (1000000 / 1212843) ≤ (192967191 / 1000000000) := by
  have h := checkLog_sound (w := (212843 / 2212843)) (n := 12)
    (lo := (19296719 / 100000000)) (hi := (192967191 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1212843 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1212843 / 1000000) = 1/(1000000 / 1212843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11315 : Bounds (19296719 / 100000000) (192967191 / 1000000000) (Real.log (1212843 / 1000000)) := by
  have h := reflection_log_11315_neg
  have he : Real.log (1212843 / 1000000) = -Real.log (1000000 / 1212843) := by
    rw [show ((1212843 / 1000000) : ℝ) = ((1000000 / 1212843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11316_neg : (119663779 / 500000000) ≤ -Real.log (787157 / 1000000) ∧
    -Real.log (787157 / 1000000) ≤ (239327559 / 1000000000) := by
  have h := checkLog_sound (w := (212843 / 1787157)) (n := 12)
    (lo := (119663779 / 500000000)) (hi := (239327559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 787157) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 787157) = 1/(787157 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11316 : Bounds (-239327559 / 1000000000) (-119663779 / 500000000) (Real.log (787157 / 1000000)) := by
  have h := reflection_log_11316_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11317_neg : (2897523 / 62500000) ≤ -Real.log (954697857351 / 1000000000000) ∧
    -Real.log (954697857351 / 1000000000000) ≤ (46360369 / 1000000000) := by
  have h := checkLog_sound (w := (45302142649 / 1954697857351)) (n := 12)
    (lo := (2897523 / 62500000)) (hi := (46360369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 954697857351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 954697857351) = 1/(954697857351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11317 : Bounds (-46360369 / 1000000000) (-2897523 / 62500000) (Real.log (954697857351 / 1000000000000)) := by
  have h := reflection_log_11317_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11318_neg : (45938699 / 1000000000) ≤ -Real.log (38204020359 / 40000000000) ∧
    -Real.log (38204020359 / 40000000000) ≤ (459387 / 10000000) := by
  have h := checkLog_sound (w := (1795979641 / 78204020359)) (n := 12)
    (lo := (45938699 / 1000000000)) (hi := (459387 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38204020359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38204020359) = 1/(38204020359 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11318 : Bounds (-459387 / 10000000) (-45938699 / 1000000000) (Real.log (38204020359 / 40000000000)) := by
  have h := reflection_log_11318_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11319_neg : (430309199 / 1000000000) ≤ -Real.log (500000000000 / 768866458149) ∧
    -Real.log (500000000000 / 768866458149) ≤ (1075773 / 2500000) := by
  have h := checkLog_sound (w := (268866458149 / 1268866458149)) (n := 12)
    (lo := (430309199 / 1000000000)) (hi := (1075773 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((768866458149 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(768866458149 / 500000000000) = 1/(500000000000 / 768866458149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11319 : Bounds (430309199 / 1000000000) (1075773 / 2500000) (Real.log (768866458149 / 500000000000)) := by
  have h := reflection_log_11319_neg
  have he : Real.log (768866458149 / 500000000000) = -Real.log (500000000000 / 768866458149) := by
    rw [show ((768866458149 / 500000000000) : ℝ) = ((500000000000 / 768866458149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11320_neg : (432294749 / 1000000000) ≤ -Real.log (250000000000 / 385197298633) ∧
    -Real.log (250000000000 / 385197298633) ≤ (1729179 / 4000000) := by
  have h := checkLog_sound (w := (135197298633 / 635197298633)) (n := 12)
    (lo := (432294749 / 1000000000)) (hi := (1729179 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((385197298633 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(385197298633 / 250000000000) = 1/(250000000000 / 385197298633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11320 : Bounds (432294749 / 1000000000) (1729179 / 4000000) (Real.log (385197298633 / 250000000000)) := by
  have h := reflection_log_11320_neg
  have he : Real.log (385197298633 / 250000000000) = -Real.log (250000000000 / 385197298633) := by
    rw [show ((385197298633 / 250000000000) : ℝ) = ((250000000000 / 385197298633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11321_neg : (873627767 / 1000000000) ≤ -Real.log (500000000000 / 1197792869269) ∧
    -Real.log (500000000000 / 1197792869269) ≤ (873627769 / 1000000000) := by
  have h := checkLog_sound (w := (197792869269 / 2197792869269)) (n := 12)
    (lo := (180480587 / 1000000000)) (hi := (45120147 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1197792869269 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1197792869269 / 1000000000000) = 1/(500000000000 / 1197792869269) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11321 : Bounds (873627767 / 1000000000) (873627769 / 1000000000) (Real.log (1197792869269 / 500000000000)) := by
  have h := reflection_log_11321_neg
  have he : Real.log (1197792869269 / 500000000000) = -Real.log (500000000000 / 1197792869269) := by
    rw [show ((1197792869269 / 500000000000) : ℝ) = ((500000000000 / 1197792869269) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11322_neg : (876035469 / 1000000000) ≤ -Real.log (500000000000 / 1200680272109) ∧
    -Real.log (500000000000 / 1200680272109) ≤ (876035471 / 1000000000) := by
  have h := checkLog_sound (w := (200680272109 / 2200680272109)) (n := 12)
    (lo := (182888289 / 1000000000)) (hi := (18288829 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1200680272109 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1200680272109 / 1000000000000) = 1/(500000000000 / 1200680272109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11322 : Bounds (876035469 / 1000000000) (876035471 / 1000000000) (Real.log (1200680272109 / 500000000000)) := by
  have h := reflection_log_11322_neg
  have he : Real.log (1200680272109 / 500000000000) = -Real.log (500000000000 / 1200680272109) := by
    rw [show ((1200680272109 / 500000000000) : ℝ) = ((500000000000 / 1200680272109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11323_neg : (345715103 / 1000000000) ≤ -Real.log (1000 / 1413) ∧
    -Real.log (1000 / 1413) ≤ (10803597 / 31250000) := by
  have h := checkLog_sound (w := (413 / 2413)) (n := 12)
    (lo := (345715103 / 1000000000)) (hi := (10803597 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1413 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1413 / 1000) = 1/(1000 / 1413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11323 : Bounds (345715103 / 1000000000) (10803597 / 31250000) (Real.log (1413 / 1000)) := by
  have h := reflection_log_11323_neg
  have he : Real.log (1413 / 1000) = -Real.log (1000 / 1413) := by
    rw [show ((1413 / 1000) : ℝ) = ((1000 / 1413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11324_neg : (532730459 / 1000000000) ≤ -Real.log (587 / 1000) ∧
    -Real.log (587 / 1000) ≤ (26636523 / 50000000) := by
  have h := checkLog_sound (w := (413 / 1587)) (n := 12)
    (lo := (532730459 / 1000000000)) (hi := (26636523 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 587) = 1/(587 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11324 : Bounds (-26636523 / 50000000) (-532730459 / 1000000000) (Real.log (587 / 1000)) := by
  have h := reflection_log_11324_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11325_neg : (206457 / 500000000) ≤ -Real.log (1000000 / 1000413) ∧
    -Real.log (1000000 / 1000413) ≤ (82583 / 200000000) := by
  have h := checkLog_sound (w := (413 / 2000413)) (n := 12)
    (lo := (206457 / 500000000)) (hi := (82583 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000413 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000413 / 1000000) = 1/(1000000 / 1000413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11325 : Bounds (206457 / 500000000) (82583 / 200000000) (Real.log (1000413 / 1000000)) := by
  have h := reflection_log_11325_neg
  have he : Real.log (1000413 / 1000000) = -Real.log (1000000 / 1000413) := by
    rw [show ((1000413 / 1000000) : ℝ) = ((1000000 / 1000413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_11326_neg : (82617 / 200000000) ≤ -Real.log (999587 / 1000000) ∧
    -Real.log (999587 / 1000000) ≤ (206543 / 500000000) := by
  have h := checkLog_sound (w := (413 / 1999587)) (n := 12)
    (lo := (82617 / 200000000)) (hi := (206543 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999587) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999587) = 1/(999587 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11326 : Bounds (-206543 / 500000000) (-82617 / 200000000) (Real.log (999587 / 1000000)) := by
  have h := reflection_log_11326_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11327_neg : (192638157 / 1000000000) ≤ -Real.log (250000 / 303111) ∧
    -Real.log (250000 / 303111) ≤ (96319079 / 500000000) := by
  have h := checkLog_sound (w := (53111 / 553111)) (n := 12)
    (lo := (192638157 / 1000000000)) (hi := (96319079 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((303111 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(303111 / 250000) = 1/(250000 / 303111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11327 : Bounds (192638157 / 1000000000) (96319079 / 500000000) (Real.log (303111 / 250000)) := by
  have h := reflection_log_11327_neg
  have he : Real.log (303111 / 250000) = -Real.log (250000 / 303111) := by
    rw [show ((303111 / 250000) : ℝ) = ((250000 / 303111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
