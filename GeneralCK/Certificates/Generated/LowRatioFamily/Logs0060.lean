import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_3840_neg : (93455001 / 1000000000) ≤ -Real.log (910779 / 1000000) ∧
    -Real.log (910779 / 1000000) ≤ (46727501 / 500000000) := by
  have h := checkLog_sound (w := (89221 / 1910779)) (n := 12)
    (lo := (93455001 / 1000000000)) (hi := (46727501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910779) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910779) = 1/(910779 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3840 : Bounds (-46727501 / 500000000) (-93455001 / 1000000000) (Real.log (910779 / 1000000)) := by
  have h := reflection_log_3840_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3841_neg : (85672981 / 1000000000) ≤ -Real.log (20000 / 21789) ∧
    -Real.log (20000 / 21789) ≤ (42836491 / 500000000) := by
  have h := checkLog_sound (w := (1789 / 41789)) (n := 12)
    (lo := (85672981 / 1000000000)) (hi := (42836491 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21789 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21789 / 20000) = 1/(20000 / 21789) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3841 : Bounds (85672981 / 1000000000) (42836491 / 500000000) (Real.log (21789 / 20000)) := by
  have h := reflection_log_3841_neg
  have he : Real.log (21789 / 20000) = -Real.log (20000 / 21789) := by
    rw [show ((21789 / 20000) : ℝ) = ((20000 / 21789) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3842_neg : (46853233 / 500000000) ≤ -Real.log (18211 / 20000) ∧
    -Real.log (18211 / 20000) ≤ (93706467 / 1000000000) := by
  have h := checkLog_sound (w := (1789 / 38211)) (n := 12)
    (lo := (46853233 / 500000000)) (hi := (93706467 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 18211) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 18211) = 1/(18211 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3842 : Bounds (-93706467 / 1000000000) (-46853233 / 500000000) (Real.log (18211 / 20000)) := by
  have h := reflection_log_3842_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3843_neg : (2008371 / 250000000) ≤ -Real.log (396799479 / 400000000) ∧
    -Real.log (396799479 / 400000000) ≤ (1606697 / 200000000) := by
  have h := checkLog_sound (w := (3200521 / 796799479)) (n := 12)
    (lo := (2008371 / 250000000)) (hi := (1606697 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 396799479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 396799479) = 1/(396799479 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3843 : Bounds (-1606697 / 200000000) (-2008371 / 250000000) (Real.log (396799479 / 400000000)) := by
  have h := reflection_log_3843_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3844_neg : (7992239 / 1000000000) ≤ -Real.log (992039613159 / 1000000000000) ∧
    -Real.log (992039613159 / 1000000000000) ≤ (99903 / 12500000) := by
  have h := checkLog_sound (w := (7960386841 / 1992039613159)) (n := 12)
    (lo := (7992239 / 1000000000)) (hi := (99903 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992039613159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992039613159) = 1/(992039613159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3844 : Bounds (-99903 / 12500000) (-7992239 / 1000000000) (Real.log (992039613159 / 1000000000000)) := by
  have h := reflection_log_3844_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3845_neg : (178917763 / 1000000000) ≤ -Real.log (100000000000 / 119592239171) ∧
    -Real.log (100000000000 / 119592239171) ≤ (44729441 / 250000000) := by
  have h := checkLog_sound (w := (19592239171 / 219592239171)) (n := 12)
    (lo := (178917763 / 1000000000)) (hi := (44729441 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((119592239171 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(119592239171 / 100000000000) = 1/(100000000000 / 119592239171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3845 : Bounds (178917763 / 1000000000) (44729441 / 250000000) (Real.log (119592239171 / 100000000000)) := by
  have h := reflection_log_3845_neg
  have he : Real.log (119592239171 / 100000000000) = -Real.log (100000000000 / 119592239171) := by
    rw [show ((119592239171 / 100000000000) : ℝ) = ((100000000000 / 119592239171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3846_neg : (22422431 / 125000000) ≤ -Real.log (500000000000 / 598237329087) ∧
    -Real.log (500000000000 / 598237329087) ≤ (179379449 / 1000000000) := by
  have h := checkLog_sound (w := (98237329087 / 1098237329087)) (n := 12)
    (lo := (22422431 / 125000000)) (hi := (179379449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598237329087 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598237329087 / 500000000000) = 1/(500000000000 / 598237329087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3846 : Bounds (22422431 / 125000000) (179379449 / 1000000000) (Real.log (598237329087 / 500000000000)) := by
  have h := reflection_log_3846_neg
  have he : Real.log (598237329087 / 500000000000) = -Real.log (500000000000 / 598237329087) := by
    rw [show ((598237329087 / 500000000000) : ℝ) = ((500000000000 / 598237329087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3847_neg : (359006853 / 1000000000) ≤ -Real.log (1953125000 / 2796692607) ∧
    -Real.log (1953125000 / 2796692607) ≤ (179503427 / 500000000) := by
  have h := checkLog_sound (w := (843567607 / 4749817607)) (n := 12)
    (lo := (359006853 / 1000000000)) (hi := (179503427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2796692607 / 1953125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2796692607 / 1953125000) = 1/(1953125000 / 2796692607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3847 : Bounds (359006853 / 1000000000) (179503427 / 500000000) (Real.log (2796692607 / 1953125000)) := by
  have h := reflection_log_3847_neg
  have he : Real.log (2796692607 / 1953125000) = -Real.log (1953125000 / 2796692607) := by
    rw [show ((2796692607 / 1953125000) : ℝ) = ((1953125000 / 2796692607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3848_neg : (35921337 / 100000000) ≤ -Real.log (500000000000 / 716101179619) ∧
    -Real.log (500000000000 / 716101179619) ≤ (359213371 / 1000000000) := by
  have h := checkLog_sound (w := (216101179619 / 1216101179619)) (n := 12)
    (lo := (35921337 / 100000000)) (hi := (359213371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((716101179619 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(716101179619 / 500000000000) = 1/(500000000000 / 716101179619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3848 : Bounds (35921337 / 100000000) (359213371 / 1000000000) (Real.log (716101179619 / 500000000000)) := by
  have h := reflection_log_3848_neg
  have he : Real.log (716101179619 / 500000000000) = -Real.log (500000000000 / 716101179619) := by
    rw [show ((716101179619 / 500000000000) : ℝ) = ((500000000000 / 716101179619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3849_neg : (163648291 / 1000000000) ≤ -Real.log (5000 / 5889) ∧
    -Real.log (5000 / 5889) ≤ (40912073 / 250000000) := by
  have h := checkLog_sound (w := (889 / 10889)) (n := 12)
    (lo := (163648291 / 1000000000)) (hi := (40912073 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5889 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5889 / 5000) = 1/(5000 / 5889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3849 : Bounds (163648291 / 1000000000) (40912073 / 250000000) (Real.log (5889 / 5000)) := by
  have h := reflection_log_3849_neg
  have he : Real.log (5889 / 5000) = -Real.log (5000 / 5889) := by
    rw [show ((5889 / 5000) : ℝ) = ((5000 / 5889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3850_neg : (48942901 / 250000000) ≤ -Real.log (4111 / 5000) ∧
    -Real.log (4111 / 5000) ≤ (39154321 / 200000000) := by
  have h := checkLog_sound (w := (889 / 9111)) (n := 12)
    (lo := (48942901 / 250000000)) (hi := (39154321 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4111) = 1/(4111 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3850 : Bounds (-39154321 / 200000000) (-48942901 / 250000000) (Real.log (4111 / 5000)) := by
  have h := reflection_log_3850_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3851_neg : (22223 / 125000000) ≤ -Real.log (5000000 / 5000889) ∧
    -Real.log (5000000 / 5000889) ≤ (35557 / 200000000) := by
  have h := checkLog_sound (w := (889 / 10000889)) (n := 12)
    (lo := (22223 / 125000000)) (hi := (35557 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000889 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000889 / 5000000) = 1/(5000000 / 5000889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3851 : Bounds (22223 / 125000000) (35557 / 200000000) (Real.log (5000889 / 5000000)) := by
  have h := reflection_log_3851_neg
  have he : Real.log (5000889 / 5000000) = -Real.log (5000000 / 5000889) := by
    rw [show ((5000889 / 5000000) : ℝ) = ((5000000 / 5000889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3852_neg : (35563 / 200000000) ≤ -Real.log (4999111 / 5000000) ∧
    -Real.log (4999111 / 5000000) ≤ (22227 / 125000000) := by
  have h := checkLog_sound (w := (889 / 9999111)) (n := 12)
    (lo := (35563 / 200000000)) (hi := (22227 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999111) = 1/(4999111 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3852 : Bounds (-22227 / 125000000) (-35563 / 200000000) (Real.log (4999111 / 5000000)) := by
  have h := reflection_log_3852_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3853_neg : (85509583 / 1000000000) ≤ -Real.log (125000 / 136159) ∧
    -Real.log (125000 / 136159) ≤ (5344349 / 62500000) := by
  have h := checkLog_sound (w := (11159 / 261159)) (n := 12)
    (lo := (85509583 / 1000000000)) (hi := (5344349 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136159 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136159 / 125000) = 1/(125000 / 136159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3853 : Bounds (85509583 / 1000000000) (5344349 / 62500000) (Real.log (136159 / 125000)) := by
  have h := reflection_log_3853_neg
  have he : Real.log (136159 / 125000) = -Real.log (125000 / 136159) := by
    rw [show ((136159 / 125000) : ℝ) = ((125000 / 136159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3854_neg : (93510999 / 1000000000) ≤ -Real.log (113841 / 125000) ∧
    -Real.log (113841 / 125000) ≤ (93511 / 1000000) := by
  have h := checkLog_sound (w := (11159 / 238841)) (n := 12)
    (lo := (93510999 / 1000000000)) (hi := (93511 / 1000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113841) = 1/(113841 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3854 : Bounds (-93511 / 1000000) (-93510999 / 1000000000) (Real.log (113841 / 125000)) := by
  have h := reflection_log_3854_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3855_neg : (685751 / 8000000) ≤ -Real.log (2000 / 2179) ∧
    -Real.log (2000 / 2179) ≤ (21429719 / 250000000) := by
  have h := checkLog_sound (w := (179 / 4179)) (n := 12)
    (lo := (685751 / 8000000)) (hi := (21429719 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2179 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2179 / 2000) = 1/(2000 / 2179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3855 : Bounds (685751 / 8000000) (21429719 / 250000000) (Real.log (2179 / 2000)) := by
  have h := reflection_log_3855_neg
  have he : Real.log (2179 / 2000) = -Real.log (2000 / 2179) := by
    rw [show ((2179 / 2000) : ℝ) = ((2000 / 2179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3856_neg : (93761379 / 1000000000) ≤ -Real.log (1821 / 2000) ∧
    -Real.log (1821 / 2000) ≤ (4688069 / 50000000) := by
  have h := checkLog_sound (w := (179 / 3821)) (n := 12)
    (lo := (93761379 / 1000000000)) (hi := (4688069 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1821) = 1/(1821 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3856 : Bounds (-4688069 / 50000000) (-93761379 / 1000000000) (Real.log (1821 / 2000)) := by
  have h := reflection_log_3856_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3857_neg : (1005313 / 125000000) ≤ -Real.log (3967959 / 4000000) ∧
    -Real.log (3967959 / 4000000) ≤ (1608501 / 200000000) := by
  have h := checkLog_sound (w := (32041 / 7967959)) (n := 12)
    (lo := (1005313 / 125000000)) (hi := (1608501 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000000 / 3967959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000000 / 3967959) = 1/(3967959 / 4000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3857 : Bounds (-1608501 / 200000000) (-1005313 / 125000000) (Real.log (3967959 / 4000000)) := by
  have h := reflection_log_3857_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3858_neg : (1000177 / 125000000) ≤ -Real.log (15500476719 / 15625000000) ∧
    -Real.log (15500476719 / 15625000000) ≤ (8001417 / 1000000000) := by
  have h := checkLog_sound (w := (124523281 / 31125476719)) (n := 12)
    (lo := (1000177 / 125000000)) (hi := (8001417 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15500476719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15500476719) = 1/(15500476719 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3858 : Bounds (-8001417 / 1000000000) (-1000177 / 125000000) (Real.log (15500476719 / 15625000000)) := by
  have h := reflection_log_3858_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3859_neg : (89510291 / 500000000) ≤ -Real.log (125000000000 / 149505670189) ∧
    -Real.log (125000000000 / 149505670189) ≤ (179020583 / 1000000000) := by
  have h := checkLog_sound (w := (24505670189 / 274505670189)) (n := 12)
    (lo := (89510291 / 500000000)) (hi := (179020583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149505670189 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149505670189 / 125000000000) = 1/(125000000000 / 149505670189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3859 : Bounds (89510291 / 500000000) (179020583 / 1000000000) (Real.log (149505670189 / 125000000000)) := by
  have h := reflection_log_3859_neg
  have he : Real.log (149505670189 / 125000000000) = -Real.log (125000000000 / 149505670189) := by
    rw [show ((149505670189 / 125000000000) : ℝ) = ((125000000000 / 149505670189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3860_neg : (35896051 / 200000000) ≤ -Real.log (500000000000 / 598297638661) ∧
    -Real.log (500000000000 / 598297638661) ≤ (2804379 / 15625000) := by
  have h := checkLog_sound (w := (98297638661 / 1098297638661)) (n := 12)
    (lo := (35896051 / 200000000)) (hi := (2804379 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598297638661 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598297638661 / 500000000000) = 1/(500000000000 / 598297638661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3860 : Bounds (35896051 / 200000000) (2804379 / 15625000) (Real.log (598297638661 / 500000000000)) := by
  have h := reflection_log_3860_neg
  have he : Real.log (598297638661 / 500000000000) = -Real.log (500000000000 / 598297638661) := by
    rw [show ((598297638661 / 500000000000) : ℝ) = ((500000000000 / 598297638661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3861_neg : (35921337 / 100000000) ≤ -Real.log (250000000000 / 358050589809) ∧
    -Real.log (250000000000 / 358050589809) ≤ (359213371 / 1000000000) := by
  have h := checkLog_sound (w := (108050589809 / 608050589809)) (n := 12)
    (lo := (35921337 / 100000000)) (hi := (359213371 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358050589809 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358050589809 / 250000000000) = 1/(250000000000 / 358050589809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3861 : Bounds (35921337 / 100000000) (359213371 / 1000000000) (Real.log (358050589809 / 250000000000)) := by
  have h := reflection_log_3861_neg
  have he : Real.log (358050589809 / 250000000000) = -Real.log (250000000000 / 358050589809) := by
    rw [show ((358050589809 / 250000000000) : ℝ) = ((250000000000 / 358050589809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3862_neg : (44927487 / 125000000) ≤ -Real.log (250000000000 / 358124543907) ∧
    -Real.log (250000000000 / 358124543907) ≤ (359419897 / 1000000000) := by
  have h := checkLog_sound (w := (108124543907 / 608124543907)) (n := 12)
    (lo := (44927487 / 125000000)) (hi := (359419897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358124543907 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358124543907 / 250000000000) = 1/(250000000000 / 358124543907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3862 : Bounds (44927487 / 125000000) (359419897 / 1000000000) (Real.log (358124543907 / 250000000000)) := by
  have h := reflection_log_3862_neg
  have he : Real.log (358124543907 / 250000000000) = -Real.log (250000000000 / 358124543907) := by
    rw [show ((358124543907 / 250000000000) : ℝ) = ((250000000000 / 358124543907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3863_neg : (163733191 / 1000000000) ≤ -Real.log (10000 / 11779) ∧
    -Real.log (10000 / 11779) ≤ (20466649 / 125000000) := by
  have h := checkLog_sound (w := (1779 / 21779)) (n := 12)
    (lo := (163733191 / 1000000000)) (hi := (20466649 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11779 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11779 / 10000) = 1/(10000 / 11779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3863 : Bounds (163733191 / 1000000000) (20466649 / 125000000) (Real.log (11779 / 10000)) := by
  have h := reflection_log_3863_neg
  have he : Real.log (11779 / 10000) = -Real.log (10000 / 11779) := by
    rw [show ((11779 / 10000) : ℝ) = ((10000 / 11779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3864_neg : (48973309 / 250000000) ≤ -Real.log (8221 / 10000) ∧
    -Real.log (8221 / 10000) ≤ (195893237 / 1000000000) := by
  have h := checkLog_sound (w := (1779 / 18221)) (n := 12)
    (lo := (48973309 / 250000000)) (hi := (195893237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8221) = 1/(8221 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3864 : Bounds (-195893237 / 1000000000) (-48973309 / 250000000) (Real.log (8221 / 10000)) := by
  have h := reflection_log_3864_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3865_neg : (44471 / 250000000) ≤ -Real.log (10000000 / 10001779) ∧
    -Real.log (10000000 / 10001779) ≤ (35577 / 200000000) := by
  have h := checkLog_sound (w := (1779 / 20001779)) (n := 12)
    (lo := (44471 / 250000000)) (hi := (35577 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001779 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001779 / 10000000) = 1/(10000000 / 10001779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3865 : Bounds (44471 / 250000000) (35577 / 200000000) (Real.log (10001779 / 10000000)) := by
  have h := reflection_log_3865_neg
  have he : Real.log (10001779 / 10000000) = -Real.log (10000000 / 10001779) := by
    rw [show ((10001779 / 10000000) : ℝ) = ((10000000 / 10001779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3866_neg : (35583 / 200000000) ≤ -Real.log (9998221 / 10000000) ∧
    -Real.log (9998221 / 10000000) ≤ (44479 / 250000000) := by
  have h := checkLog_sound (w := (1779 / 19998221)) (n := 12)
    (lo := (35583 / 200000000)) (hi := (44479 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998221) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998221) = 1/(9998221 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3866 : Bounds (-44479 / 250000000) (-35583 / 200000000) (Real.log (9998221 / 10000000)) := by
  have h := reflection_log_3866_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3867_neg : (42778201 / 500000000) ≤ -Real.log (1000000 / 1089323) ∧
    -Real.log (1000000 / 1089323) ≤ (85556403 / 1000000000) := by
  have h := checkLog_sound (w := (89323 / 2089323)) (n := 12)
    (lo := (42778201 / 500000000)) (hi := (85556403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089323 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089323 / 1000000) = 1/(1000000 / 1089323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3867 : Bounds (42778201 / 500000000) (85556403 / 1000000000) (Real.log (1089323 / 1000000)) := by
  have h := reflection_log_3867_neg
  have he : Real.log (1089323 / 1000000) = -Real.log (1000000 / 1089323) := by
    rw [show ((1089323 / 1000000) : ℝ) = ((1000000 / 1089323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3868_neg : (93567 / 1000000) ≤ -Real.log (910677 / 1000000) ∧
    -Real.log (910677 / 1000000) ≤ (93567001 / 1000000000) := by
  have h := checkLog_sound (w := (89323 / 1910677)) (n := 12)
    (lo := (93567 / 1000000)) (hi := (93567001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910677) = 1/(910677 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3868 : Bounds (-93567001 / 1000000000) (-93567 / 1000000) (Real.log (910677 / 1000000)) := by
  have h := reflection_log_3868_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3869_neg : (21441421 / 250000000) ≤ -Real.log (1000000 / 1089551) ∧
    -Real.log (1000000 / 1089551) ≤ (17153137 / 200000000) := by
  have h := checkLog_sound (w := (89551 / 2089551)) (n := 12)
    (lo := (21441421 / 250000000)) (hi := (17153137 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089551 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089551 / 1000000) = 1/(1000000 / 1089551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3869 : Bounds (21441421 / 250000000) (17153137 / 200000000) (Real.log (1089551 / 1000000)) := by
  have h := reflection_log_3869_neg
  have he : Real.log (1089551 / 1000000) = -Real.log (1000000 / 1089551) := by
    rw [show ((1089551 / 1000000) : ℝ) = ((1000000 / 1089551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3870_neg : (46908697 / 500000000) ≤ -Real.log (910449 / 1000000) ∧
    -Real.log (910449 / 1000000) ≤ (18763479 / 200000000) := by
  have h := checkLog_sound (w := (89551 / 1910449)) (n := 12)
    (lo := (46908697 / 500000000)) (hi := (18763479 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910449) = 1/(910449 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3870 : Bounds (-18763479 / 200000000) (-46908697 / 500000000) (Real.log (910449 / 1000000)) := by
  have h := reflection_log_3870_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3871_neg : (8051709 / 1000000000) ≤ -Real.log (991980618399 / 1000000000000) ∧
    -Real.log (991980618399 / 1000000000000) ≤ (805171 / 100000000) := by
  have h := checkLog_sound (w := (8019381601 / 1991980618399)) (n := 12)
    (lo := (8051709 / 1000000000)) (hi := (805171 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991980618399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991980618399) = 1/(991980618399 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3871 : Bounds (-805171 / 100000000) (-8051709 / 1000000000) (Real.log (991980618399 / 1000000000000)) := by
  have h := reflection_log_3871_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3872_neg : (8010597 / 1000000000) ≤ -Real.log (992021401671 / 1000000000000) ∧
    -Real.log (992021401671 / 1000000000000) ≤ (4005299 / 500000000) := by
  have h := checkLog_sound (w := (7978598329 / 1992021401671)) (n := 12)
    (lo := (8010597 / 1000000000)) (hi := (4005299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992021401671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992021401671) = 1/(992021401671 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3872 : Bounds (-4005299 / 500000000) (-8010597 / 1000000000) (Real.log (992021401671 / 1000000000000)) := by
  have h := reflection_log_3872_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3873_neg : (89561701 / 500000000) ≤ -Real.log (1953125000 / 2336266299) ∧
    -Real.log (1953125000 / 2336266299) ≤ (179123403 / 1000000000) := by
  have h := checkLog_sound (w := (383141299 / 4289391299)) (n := 12)
    (lo := (89561701 / 500000000)) (hi := (179123403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2336266299 / 1953125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2336266299 / 1953125000) = 1/(1953125000 / 2336266299) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3873 : Bounds (89561701 / 500000000) (179123403 / 1000000000) (Real.log (2336266299 / 1953125000)) := by
  have h := reflection_log_3873_neg
  have he : Real.log (2336266299 / 1953125000) = -Real.log (1953125000 / 2336266299) := by
    rw [show ((2336266299 / 1953125000) : ℝ) = ((1953125000 / 2336266299) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3874_neg : (179583079 / 1000000000) ≤ -Real.log (400000000 / 478687329) ∧
    -Real.log (400000000 / 478687329) ≤ (4489577 / 25000000) := by
  have h := checkLog_sound (w := (78687329 / 878687329)) (n := 12)
    (lo := (179583079 / 1000000000)) (hi := (4489577 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((478687329 / 400000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(478687329 / 400000000) = 1/(400000000 / 478687329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3874 : Bounds (179583079 / 1000000000) (4489577 / 25000000) (Real.log (478687329 / 400000000)) := by
  have h := reflection_log_3874_neg
  have he : Real.log (478687329 / 400000000) = -Real.log (400000000 / 478687329) := by
    rw [show ((478687329 / 400000000) : ℝ) = ((400000000 / 478687329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3875_neg : (44927487 / 125000000) ≤ -Real.log (500000000000 / 716249087813) ∧
    -Real.log (500000000000 / 716249087813) ≤ (359419897 / 1000000000) := by
  have h := checkLog_sound (w := (216249087813 / 1216249087813)) (n := 12)
    (lo := (44927487 / 125000000)) (hi := (359419897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((716249087813 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(716249087813 / 500000000000) = 1/(500000000000 / 716249087813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3875 : Bounds (44927487 / 125000000) (359419897 / 1000000000) (Real.log (716249087813 / 500000000000)) := by
  have h := reflection_log_3875_neg
  have he : Real.log (716249087813 / 500000000000) = -Real.log (500000000000 / 716249087813) := by
    rw [show ((716249087813 / 500000000000) : ℝ) = ((500000000000 / 716249087813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3876_neg : (89906607 / 250000000) ≤ -Real.log (62500000000 / 89549628999) ∧
    -Real.log (62500000000 / 89549628999) ≤ (359626429 / 1000000000) := by
  have h := checkLog_sound (w := (27049628999 / 152049628999)) (n := 12)
    (lo := (89906607 / 250000000)) (hi := (359626429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89549628999 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89549628999 / 62500000000) = 1/(62500000000 / 89549628999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3876 : Bounds (89906607 / 250000000) (359626429 / 1000000000) (Real.log (89549628999 / 62500000000)) := by
  have h := reflection_log_3876_neg
  have he : Real.log (89549628999 / 62500000000) = -Real.log (62500000000 / 89549628999) := by
    rw [show ((89549628999 / 62500000000) : ℝ) = ((62500000000 / 89549628999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3877_neg : (32763617 / 200000000) ≤ -Real.log (500 / 589) ∧
    -Real.log (500 / 589) ≤ (81909043 / 500000000) := by
  have h := checkLog_sound (w := (89 / 1089)) (n := 12)
    (lo := (32763617 / 200000000)) (hi := (81909043 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589 / 500) = 1/(500 / 589) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3877 : Bounds (32763617 / 200000000) (81909043 / 500000000) (Real.log (589 / 500)) := by
  have h := reflection_log_3877_neg
  have he : Real.log (589 / 500) = -Real.log (500 / 589) := by
    rw [show ((589 / 500) : ℝ) = ((500 / 589) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3878_neg : (196014883 / 1000000000) ≤ -Real.log (411 / 500) ∧
    -Real.log (411 / 500) ≤ (49003721 / 250000000) := by
  have h := checkLog_sound (w := (89 / 911)) (n := 12)
    (lo := (196014883 / 1000000000)) (hi := (49003721 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 411) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 411) = 1/(411 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3878 : Bounds (-49003721 / 250000000) (-196014883 / 1000000000) (Real.log (411 / 500)) := by
  have h := reflection_log_3878_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3879_neg : (2781 / 15625000) ≤ -Real.log (500000 / 500089) ∧
    -Real.log (500000 / 500089) ≤ (35597 / 200000000) := by
  have h := checkLog_sound (w := (89 / 1000089)) (n := 12)
    (lo := (2781 / 15625000)) (hi := (35597 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500089 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500089 / 500000) = 1/(500000 / 500089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3879 : Bounds (2781 / 15625000) (35597 / 200000000) (Real.log (500089 / 500000)) := by
  have h := reflection_log_3879_neg
  have he : Real.log (500089 / 500000) = -Real.log (500000 / 500089) := by
    rw [show ((500089 / 500000) : ℝ) = ((500000 / 500089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3880_neg : (35603 / 200000000) ≤ -Real.log (499911 / 500000) ∧
    -Real.log (499911 / 500000) ≤ (5563 / 31250000) := by
  have h := checkLog_sound (w := (89 / 999911)) (n := 12)
    (lo := (35603 / 200000000)) (hi := (5563 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499911) = 1/(499911 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3880 : Bounds (-5563 / 31250000) (-35603 / 200000000) (Real.log (499911 / 500000)) := by
  have h := reflection_log_3880_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3881_neg : (85602301 / 1000000000) ≤ -Real.log (1000000 / 1089373) ∧
    -Real.log (1000000 / 1089373) ≤ (42801151 / 500000000) := by
  have h := checkLog_sound (w := (89373 / 2089373)) (n := 12)
    (lo := (85602301 / 1000000000)) (hi := (42801151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089373 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089373 / 1000000) = 1/(1000000 / 1089373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3881 : Bounds (85602301 / 1000000000) (42801151 / 500000000) (Real.log (1089373 / 1000000)) := by
  have h := reflection_log_3881_neg
  have he : Real.log (1089373 / 1000000) = -Real.log (1000000 / 1089373) := by
    rw [show ((1089373 / 1000000) : ℝ) = ((1000000 / 1089373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3882_neg : (18724381 / 200000000) ≤ -Real.log (910627 / 1000000) ∧
    -Real.log (910627 / 1000000) ≤ (46810953 / 500000000) := by
  have h := checkLog_sound (w := (89373 / 1910627)) (n := 12)
    (lo := (18724381 / 200000000)) (hi := (46810953 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910627) = 1/(910627 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3882 : Bounds (-46810953 / 500000000) (-18724381 / 200000000) (Real.log (910627 / 1000000)) := by
  have h := reflection_log_3882_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3883_neg : (85812491 / 1000000000) ≤ -Real.log (500000 / 544801) ∧
    -Real.log (500000 / 544801) ≤ (21453123 / 250000000) := by
  have h := checkLog_sound (w := (44801 / 1044801)) (n := 12)
    (lo := (85812491 / 1000000000)) (hi := (21453123 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((544801 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(544801 / 500000) = 1/(500000 / 544801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3883 : Bounds (85812491 / 1000000000) (21453123 / 250000000) (Real.log (544801 / 500000)) := by
  have h := reflection_log_3883_neg
  have he : Real.log (544801 / 500000) = -Real.log (500000 / 544801) := by
    rw [show ((544801 / 500000) : ℝ) = ((500000 / 544801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3884_neg : (23468353 / 250000000) ≤ -Real.log (455199 / 500000) ∧
    -Real.log (455199 / 500000) ≤ (93873413 / 1000000000) := by
  have h := checkLog_sound (w := (44801 / 955199)) (n := 12)
    (lo := (23468353 / 250000000)) (hi := (93873413 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 455199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 455199) = 1/(455199 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3884 : Bounds (-93873413 / 1000000000) (-23468353 / 250000000) (Real.log (455199 / 500000)) := by
  have h := reflection_log_3884_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3885_neg : (201523 / 25000000) ≤ -Real.log (247992870399 / 250000000000) ∧
    -Real.log (247992870399 / 250000000000) ≤ (8060921 / 1000000000) := by
  have h := checkLog_sound (w := (2007129601 / 497992870399)) (n := 12)
    (lo := (201523 / 25000000)) (hi := (8060921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247992870399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247992870399) = 1/(247992870399 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3885 : Bounds (-8060921 / 1000000000) (-201523 / 25000000) (Real.log (247992870399 / 250000000000)) := by
  have h := reflection_log_3885_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3886_neg : (2004901 / 250000000) ≤ -Real.log (992012466871 / 1000000000000) ∧
    -Real.log (992012466871 / 1000000000000) ≤ (1603921 / 200000000) := by
  have h := checkLog_sound (w := (7987533129 / 1992012466871)) (n := 12)
    (lo := (2004901 / 250000000)) (hi := (1603921 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992012466871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992012466871) = 1/(992012466871 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3886 : Bounds (-1603921 / 200000000) (-2004901 / 250000000) (Real.log (992012466871 / 1000000000000)) := by
  have h := reflection_log_3886_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3887_neg : (179224207 / 1000000000) ≤ -Real.log (31250000000 / 37384029081) ∧
    -Real.log (31250000000 / 37384029081) ≤ (11201513 / 62500000) := by
  have h := checkLog_sound (w := (6134029081 / 68634029081)) (n := 12)
    (lo := (179224207 / 1000000000)) (hi := (11201513 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((37384029081 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(37384029081 / 31250000000) = 1/(31250000000 / 37384029081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3887 : Bounds (179224207 / 1000000000) (11201513 / 62500000) (Real.log (37384029081 / 31250000000)) := by
  have h := reflection_log_3887_neg
  have he : Real.log (37384029081 / 31250000000) = -Real.log (31250000000 / 37384029081) := by
    rw [show ((37384029081 / 31250000000) : ℝ) = ((31250000000 / 37384029081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3888_neg : (11230369 / 62500000) ≤ -Real.log (500000000000 / 598420690731) ∧
    -Real.log (500000000000 / 598420690731) ≤ (35937181 / 200000000) := by
  have h := checkLog_sound (w := (98420690731 / 1098420690731)) (n := 12)
    (lo := (11230369 / 62500000)) (hi := (35937181 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598420690731 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598420690731 / 500000000000) = 1/(500000000000 / 598420690731) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3888 : Bounds (11230369 / 62500000) (35937181 / 200000000) (Real.log (598420690731 / 500000000000)) := by
  have h := reflection_log_3888_neg
  have he : Real.log (598420690731 / 500000000000) = -Real.log (500000000000 / 598420690731) := by
    rw [show ((598420690731 / 500000000000) : ℝ) = ((500000000000 / 598420690731) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3889_neg : (89906607 / 250000000) ≤ -Real.log (500000000000 / 716397031991) ∧
    -Real.log (500000000000 / 716397031991) ≤ (359626429 / 1000000000) := by
  have h := checkLog_sound (w := (216397031991 / 1216397031991)) (n := 12)
    (lo := (89906607 / 250000000)) (hi := (359626429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((716397031991 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(716397031991 / 500000000000) = 1/(500000000000 / 716397031991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3889 : Bounds (89906607 / 250000000) (359626429 / 1000000000) (Real.log (716397031991 / 500000000000)) := by
  have h := reflection_log_3889_neg
  have he : Real.log (716397031991 / 500000000000) = -Real.log (500000000000 / 716397031991) := by
    rw [show ((716397031991 / 500000000000) : ℝ) = ((500000000000 / 716397031991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3890_neg : (359832969 / 1000000000) ≤ -Real.log (250000000000 / 358272506083) ∧
    -Real.log (250000000000 / 358272506083) ≤ (35983297 / 100000000) := by
  have h := checkLog_sound (w := (108272506083 / 608272506083)) (n := 12)
    (lo := (359832969 / 1000000000)) (hi := (35983297 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((358272506083 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(358272506083 / 250000000000) = 1/(250000000000 / 358272506083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3890 : Bounds (359832969 / 1000000000) (35983297 / 100000000) (Real.log (358272506083 / 250000000000)) := by
  have h := reflection_log_3890_neg
  have he : Real.log (358272506083 / 250000000000) = -Real.log (250000000000 / 358272506083) := by
    rw [show ((358272506083 / 250000000000) : ℝ) = ((250000000000 / 358272506083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3891_neg : (163902971 / 1000000000) ≤ -Real.log (10000 / 11781) ∧
    -Real.log (10000 / 11781) ≤ (40975743 / 250000000) := by
  have h := checkLog_sound (w := (1781 / 21781)) (n := 12)
    (lo := (163902971 / 1000000000)) (hi := (40975743 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11781 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11781 / 10000) = 1/(10000 / 11781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3891 : Bounds (163902971 / 1000000000) (40975743 / 250000000) (Real.log (11781 / 10000)) := by
  have h := reflection_log_3891_neg
  have he : Real.log (11781 / 10000) = -Real.log (10000 / 11781) := by
    rw [show ((11781 / 10000) : ℝ) = ((10000 / 11781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3892_neg : (39227309 / 200000000) ≤ -Real.log (8219 / 10000) ∧
    -Real.log (8219 / 10000) ≤ (98068273 / 500000000) := by
  have h := checkLog_sound (w := (1781 / 18219)) (n := 12)
    (lo := (39227309 / 200000000)) (hi := (98068273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8219) = 1/(8219 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3892 : Bounds (-98068273 / 500000000) (-39227309 / 200000000) (Real.log (8219 / 10000)) := by
  have h := reflection_log_3892_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3893_neg : (44521 / 250000000) ≤ -Real.log (10000000 / 10001781) ∧
    -Real.log (10000000 / 10001781) ≤ (35617 / 200000000) := by
  have h := checkLog_sound (w := (1781 / 20001781)) (n := 12)
    (lo := (44521 / 250000000)) (hi := (35617 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001781 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001781 / 10000000) = 1/(10000000 / 10001781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3893 : Bounds (44521 / 250000000) (35617 / 200000000) (Real.log (10001781 / 10000000)) := by
  have h := reflection_log_3893_neg
  have he : Real.log (10001781 / 10000000) = -Real.log (10000000 / 10001781) := by
    rw [show ((10001781 / 10000000) : ℝ) = ((10000000 / 10001781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3894_neg : (35623 / 200000000) ≤ -Real.log (9998219 / 10000000) ∧
    -Real.log (9998219 / 10000000) ≤ (44529 / 250000000) := by
  have h := checkLog_sound (w := (1781 / 19998219)) (n := 12)
    (lo := (35623 / 200000000)) (hi := (44529 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998219) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998219) = 1/(9998219 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3894 : Bounds (-44529 / 250000000) (-35623 / 200000000) (Real.log (9998219 / 10000000)) := by
  have h := reflection_log_3894_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3895_neg : (21412279 / 250000000) ≤ -Real.log (62500 / 68089) ∧
    -Real.log (62500 / 68089) ≤ (85649117 / 1000000000) := by
  have h := checkLog_sound (w := (5589 / 130589)) (n := 12)
    (lo := (21412279 / 250000000)) (hi := (85649117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((68089 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(68089 / 62500) = 1/(62500 / 68089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3895 : Bounds (21412279 / 250000000) (85649117 / 1000000000) (Real.log (68089 / 62500)) := by
  have h := reflection_log_3895_neg
  have he : Real.log (68089 / 62500) = -Real.log (62500 / 68089) := by
    rw [show ((68089 / 62500) : ℝ) = ((62500 / 68089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3896_neg : (11709739 / 125000000) ≤ -Real.log (56911 / 62500) ∧
    -Real.log (56911 / 62500) ≤ (93677913 / 1000000000) := by
  have h := checkLog_sound (w := (5589 / 119411)) (n := 12)
    (lo := (11709739 / 125000000)) (hi := (93677913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 56911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 56911) = 1/(56911 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3896 : Bounds (-93677913 / 1000000000) (-11709739 / 125000000) (Real.log (56911 / 62500)) := by
  have h := reflection_log_3896_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3897_neg : (2683103 / 31250000) ≤ -Real.log (1000000 / 1089653) ∧
    -Real.log (1000000 / 1089653) ≤ (85859297 / 1000000000) := by
  have h := checkLog_sound (w := (89653 / 2089653)) (n := 12)
    (lo := (2683103 / 31250000)) (hi := (85859297 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1089653 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1089653 / 1000000) = 1/(1000000 / 1089653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3897 : Bounds (2683103 / 31250000) (85859297 / 1000000000) (Real.log (1089653 / 1000000)) := by
  have h := reflection_log_3897_neg
  have he : Real.log (1089653 / 1000000) = -Real.log (1000000 / 1089653) := by
    rw [show ((1089653 / 1000000) : ℝ) = ((1000000 / 1089653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3898_neg : (93929433 / 1000000000) ≤ -Real.log (910347 / 1000000) ∧
    -Real.log (910347 / 1000000) ≤ (46964717 / 500000000) := by
  have h := checkLog_sound (w := (89653 / 1910347)) (n := 12)
    (lo := (93929433 / 1000000000)) (hi := (46964717 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 910347) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 910347) = 1/(910347 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3898 : Bounds (-46964717 / 500000000) (-93929433 / 1000000000) (Real.log (910347 / 1000000)) := by
  have h := reflection_log_3898_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3899_neg : (1008767 / 125000000) ≤ -Real.log (991962339591 / 1000000000000) ∧
    -Real.log (991962339591 / 1000000000000) ≤ (8070137 / 1000000000) := by
  have h := checkLog_sound (w := (8037660409 / 1991962339591)) (n := 12)
    (lo := (1008767 / 125000000)) (hi := (8070137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 991962339591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 991962339591) = 1/(991962339591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3899 : Bounds (-8070137 / 1000000000) (-1008767 / 125000000) (Real.log (991962339591 / 1000000000000)) := by
  have h := reflection_log_3899_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3900_neg : (2007199 / 250000000) ≤ -Real.log (3875013079 / 3906250000) ∧
    -Real.log (3875013079 / 3906250000) ≤ (8028797 / 1000000000) := by
  have h := checkLog_sound (w := (31236921 / 7781263079)) (n := 12)
    (lo := (2007199 / 250000000)) (hi := (8028797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3875013079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3875013079) = 1/(3875013079 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3900 : Bounds (-8028797 / 1000000000) (-2007199 / 250000000) (Real.log (3875013079 / 3906250000)) := by
  have h := reflection_log_3900_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3901_neg : (44831757 / 250000000) ≤ -Real.log (250000000000 / 299102985363) ∧
    -Real.log (250000000000 / 299102985363) ≤ (179327029 / 1000000000) := by
  have h := checkLog_sound (w := (49102985363 / 549102985363)) (n := 12)
    (lo := (44831757 / 250000000)) (hi := (179327029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((299102985363 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(299102985363 / 250000000000) = 1/(250000000000 / 299102985363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3901 : Bounds (44831757 / 250000000) (179327029 / 1000000000) (Real.log (299102985363 / 250000000000)) := by
  have h := reflection_log_3901_neg
  have he : Real.log (299102985363 / 250000000000) = -Real.log (250000000000 / 299102985363) := by
    rw [show ((299102985363 / 250000000000) : ℝ) = ((250000000000 / 299102985363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3902_neg : (17978873 / 100000000) ≤ -Real.log (500000000000 / 598482227107) ∧
    -Real.log (500000000000 / 598482227107) ≤ (179788731 / 1000000000) := by
  have h := checkLog_sound (w := (98482227107 / 1098482227107)) (n := 12)
    (lo := (17978873 / 100000000)) (hi := (179788731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598482227107 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(598482227107 / 500000000000) = 1/(500000000000 / 598482227107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3902 : Bounds (17978873 / 100000000) (179788731 / 1000000000) (Real.log (598482227107 / 500000000000)) := by
  have h := reflection_log_3902_neg
  have he : Real.log (598482227107 / 500000000000) = -Real.log (500000000000 / 598482227107) := by
    rw [show ((598482227107 / 500000000000) : ℝ) = ((500000000000 / 598482227107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3903_neg : (359832969 / 1000000000) ≤ -Real.log (100000000000 / 143309002433) ∧
    -Real.log (100000000000 / 143309002433) ≤ (35983297 / 100000000) := by
  have h := checkLog_sound (w := (43309002433 / 243309002433)) (n := 12)
    (lo := (359832969 / 1000000000)) (hi := (35983297 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((143309002433 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(143309002433 / 100000000000) = 1/(100000000000 / 143309002433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3903 : Bounds (359832969 / 1000000000) (35983297 / 100000000) (Real.log (143309002433 / 100000000000)) := by
  have h := reflection_log_3903_neg
  have he : Real.log (143309002433 / 100000000000) = -Real.log (100000000000 / 143309002433) := by
    rw [show ((143309002433 / 100000000000) : ℝ) = ((100000000000 / 143309002433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
