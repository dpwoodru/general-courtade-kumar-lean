import GeneralCK.Certificates.LowRatioFamilyHelpers
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_8000_neg : (14345637 / 1000000000) ≤ -Real.log (39430270839 / 40000000000) ∧
    -Real.log (39430270839 / 40000000000) ≤ (7172819 / 500000000) := by
  have h := checkLog_sound (w := (569729161 / 79430270839)) (n := 12)
    (lo := (14345637 / 1000000000)) (hi := (7172819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39430270839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39430270839) = 1/(39430270839 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8000 : Bounds (-7172819 / 500000000) (-14345637 / 1000000000) (Real.log (39430270839 / 40000000000)) := by
  have h := reflection_log_8000_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8001_neg : (119916511 / 500000000) ≤ -Real.log (62500000000 / 79439806167) ∧
    -Real.log (62500000000 / 79439806167) ≤ (239833023 / 1000000000) := by
  have h := checkLog_sound (w := (16939806167 / 141939806167)) (n := 12)
    (lo := (119916511 / 500000000)) (hi := (239833023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((79439806167 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(79439806167 / 62500000000) = 1/(62500000000 / 79439806167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8001 : Bounds (119916511 / 500000000) (239833023 / 1000000000) (Real.log (79439806167 / 62500000000)) := by
  have h := reflection_log_8001_neg
  have he : Real.log (79439806167 / 62500000000) = -Real.log (62500000000 / 79439806167) := by
    rw [show ((79439806167 / 62500000000) : ℝ) = ((62500000000 / 79439806167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8002_neg : (240833329 / 1000000000) ≤ -Real.log (500000000000 / 636154480653) ∧
    -Real.log (500000000000 / 636154480653) ≤ (24083333 / 100000000) := by
  have h := checkLog_sound (w := (136154480653 / 1136154480653)) (n := 12)
    (lo := (240833329 / 1000000000)) (hi := (24083333 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((636154480653 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(636154480653 / 500000000000) = 1/(500000000000 / 636154480653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8002 : Bounds (240833329 / 1000000000) (24083333 / 100000000) (Real.log (636154480653 / 500000000000)) := by
  have h := reflection_log_8002_neg
  have he : Real.log (636154480653 / 500000000000) = -Real.log (500000000000 / 636154480653) := by
    rw [show ((636154480653 / 500000000000) : ℝ) = ((500000000000 / 636154480653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8003_neg : (241063481 / 500000000) ≤ -Real.log (250000000000 / 404878847413) ∧
    -Real.log (250000000000 / 404878847413) ≤ (482126963 / 1000000000) := by
  have h := checkLog_sound (w := (154878847413 / 654878847413)) (n := 12)
    (lo := (241063481 / 500000000)) (hi := (482126963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((404878847413 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(404878847413 / 250000000000) = 1/(250000000000 / 404878847413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8003 : Bounds (241063481 / 500000000) (482126963 / 1000000000) (Real.log (404878847413 / 250000000000)) := by
  have h := reflection_log_8003_neg
  have he : Real.log (404878847413 / 250000000000) = -Real.log (250000000000 / 404878847413) := by
    rw [show ((404878847413 / 250000000000) : ℝ) = ((250000000000 / 404878847413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8004_neg : (483186341 / 1000000000) ≤ -Real.log (125000000000 / 202653997379) ∧
    -Real.log (125000000000 / 202653997379) ≤ (241593171 / 500000000) := by
  have h := checkLog_sound (w := (77653997379 / 327653997379)) (n := 12)
    (lo := (483186341 / 1000000000)) (hi := (241593171 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202653997379 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202653997379 / 125000000000) = 1/(125000000000 / 202653997379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8004 : Bounds (483186341 / 1000000000) (241593171 / 500000000) (Real.log (202653997379 / 125000000000)) := by
  have h := reflection_log_8004_neg
  have he : Real.log (202653997379 / 125000000000) = -Real.log (125000000000 / 202653997379) := by
    rw [show ((202653997379 / 125000000000) : ℝ) = ((125000000000 / 202653997379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8005_neg : (42618643 / 200000000) ≤ -Real.log (80 / 99) ∧
    -Real.log (80 / 99) ≤ (6659163 / 31250000) := by
  have h := checkLog_sound (w := (19 / 179)) (n := 12)
    (lo := (42618643 / 200000000)) (hi := (6659163 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99 / 80) = 1/(80 / 99) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8005 : Bounds (42618643 / 200000000) (6659163 / 31250000) (Real.log (99 / 80)) := by
  have h := reflection_log_8005_neg
  have he : Real.log (99 / 80) = -Real.log (80 / 99) := by
    rw [show ((99 / 80) : ℝ) = ((80 / 99) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8006_neg : (27115277 / 100000000) ≤ -Real.log (61 / 80) ∧
    -Real.log (61 / 80) ≤ (271152771 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 141)) (n := 12)
    (lo := (27115277 / 100000000)) (hi := (271152771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 61) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 61) = 1/(61 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8006 : Bounds (-271152771 / 1000000000) (-27115277 / 100000000) (Real.log (61 / 80)) := by
  have h := reflection_log_8006_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8007_neg : (237471 / 1000000000) ≤ -Real.log (80000 / 80019) ∧
    -Real.log (80000 / 80019) ≤ (7421 / 31250000) := by
  have h := checkLog_sound (w := (19 / 160019)) (n := 12)
    (lo := (237471 / 1000000000)) (hi := (7421 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80019 / 80000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80019 / 80000) = 1/(80000 / 80019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8007 : Bounds (237471 / 1000000000) (7421 / 31250000) (Real.log (80019 / 80000)) := by
  have h := reflection_log_8007_neg
  have he : Real.log (80019 / 80000) = -Real.log (80000 / 80019) := by
    rw [show ((80019 / 80000) : ℝ) = ((80000 / 80019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8008_neg : (29691 / 125000000) ≤ -Real.log (79981 / 80000) ∧
    -Real.log (79981 / 80000) ≤ (237529 / 1000000000) := by
  have h := checkLog_sound (w := (19 / 159981)) (n := 12)
    (lo := (29691 / 125000000)) (hi := (237529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80000 / 79981) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80000 / 79981) = 1/(79981 / 80000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8008 : Bounds (-237529 / 1000000000) (-29691 / 125000000) (Real.log (79981 / 80000)) := by
  have h := reflection_log_8008_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8009_neg : (56487079 / 500000000) ≤ -Real.log (1000000 / 1119603) ∧
    -Real.log (1000000 / 1119603) ≤ (112974159 / 1000000000) := by
  have h := checkLog_sound (w := (119603 / 2119603)) (n := 12)
    (lo := (56487079 / 500000000)) (hi := (112974159 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1119603 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1119603 / 1000000) = 1/(1000000 / 1119603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8009 : Bounds (56487079 / 500000000) (112974159 / 1000000000) (Real.log (1119603 / 1000000)) := by
  have h := reflection_log_8009_neg
  have he : Real.log (1119603 / 1000000) = -Real.log (1000000 / 1119603) := by
    rw [show ((1119603 / 1000000) : ℝ) = ((1000000 / 1119603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8010_neg : (1990349 / 15625000) ≤ -Real.log (880397 / 1000000) ∧
    -Real.log (880397 / 1000000) ≤ (127382337 / 1000000000) := by
  have h := checkLog_sound (w := (119603 / 1880397)) (n := 12)
    (lo := (1990349 / 15625000)) (hi := (127382337 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 880397) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 880397) = 1/(880397 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8010 : Bounds (-127382337 / 1000000000) (-1990349 / 15625000) (Real.log (880397 / 1000000)) := by
  have h := reflection_log_8010_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8011_neg : (22682879 / 200000000) ≤ -Real.log (31250 / 35003) ∧
    -Real.log (31250 / 35003) ≤ (28353599 / 250000000) := by
  have h := checkLog_sound (w := (3753 / 66253)) (n := 12)
    (lo := (22682879 / 200000000)) (hi := (28353599 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35003 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35003 / 31250) = 1/(31250 / 35003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8011 : Bounds (22682879 / 200000000) (28353599 / 250000000) (Real.log (35003 / 31250)) := by
  have h := reflection_log_8011_neg
  have he : Real.log (35003 / 31250) = -Real.log (31250 / 35003) := by
    rw [show ((35003 / 31250) : ℝ) = ((31250 / 35003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8012_neg : (31985617 / 250000000) ≤ -Real.log (27497 / 31250) ∧
    -Real.log (27497 / 31250) ≤ (127942469 / 1000000000) := by
  have h := checkLog_sound (w := (3753 / 58747)) (n := 12)
    (lo := (31985617 / 250000000)) (hi := (127942469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 27497) = 1/(27497 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8012 : Bounds (-127942469 / 1000000000) (-31985617 / 250000000) (Real.log (27497 / 31250)) := by
  have h := reflection_log_8012_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8013_neg : (1816009 / 125000000) ≤ -Real.log (962477491 / 976562500) ∧
    -Real.log (962477491 / 976562500) ≤ (14528073 / 1000000000) := by
  have h := checkLog_sound (w := (14085009 / 1939039991)) (n := 12)
    (lo := (1816009 / 125000000)) (hi := (14528073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 962477491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 962477491) = 1/(962477491 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8013 : Bounds (-14528073 / 1000000000) (-1816009 / 125000000) (Real.log (962477491 / 976562500)) := by
  have h := reflection_log_8013_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8014_neg : (7204089 / 500000000) ≤ -Real.log (985695122391 / 1000000000000) ∧
    -Real.log (985695122391 / 1000000000000) ≤ (14408179 / 1000000000) := by
  have h := checkLog_sound (w := (14304877609 / 1985695122391)) (n := 12)
    (lo := (7204089 / 500000000)) (hi := (14408179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 985695122391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 985695122391) = 1/(985695122391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8014 : Bounds (-14408179 / 1000000000) (-7204089 / 500000000) (Real.log (985695122391 / 1000000000000)) := by
  have h := reflection_log_8014_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8015_neg : (48071299 / 200000000) ≤ -Real.log (500000000000 / 635851212577) ∧
    -Real.log (500000000000 / 635851212577) ≤ (15022281 / 62500000) := by
  have h := checkLog_sound (w := (135851212577 / 1135851212577)) (n := 12)
    (lo := (48071299 / 200000000)) (hi := (15022281 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((635851212577 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(635851212577 / 500000000000) = 1/(500000000000 / 635851212577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8015 : Bounds (48071299 / 200000000) (15022281 / 62500000) (Real.log (635851212577 / 500000000000)) := by
  have h := reflection_log_8015_neg
  have he : Real.log (635851212577 / 500000000000) = -Real.log (500000000000 / 635851212577) := by
    rw [show ((635851212577 / 500000000000) : ℝ) = ((500000000000 / 635851212577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8016_neg : (3771201 / 15625000) ≤ -Real.log (500000000000 / 636487616831) ∧
    -Real.log (500000000000 / 636487616831) ≤ (48271373 / 200000000) := by
  have h := checkLog_sound (w := (136487616831 / 1136487616831)) (n := 12)
    (lo := (3771201 / 15625000)) (hi := (48271373 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((636487616831 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(636487616831 / 500000000000) = 1/(500000000000 / 636487616831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8016 : Bounds (3771201 / 15625000) (48271373 / 200000000) (Real.log (636487616831 / 500000000000)) := by
  have h := reflection_log_8016_neg
  have he : Real.log (636487616831 / 500000000000) = -Real.log (500000000000 / 636487616831) := by
    rw [show ((636487616831 / 500000000000) : ℝ) = ((500000000000 / 636487616831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8017_neg : (483186341 / 1000000000) ≤ -Real.log (100000000000 / 162123197903) ∧
    -Real.log (100000000000 / 162123197903) ≤ (241593171 / 500000000) := by
  have h := checkLog_sound (w := (62123197903 / 262123197903)) (n := 12)
    (lo := (483186341 / 1000000000)) (hi := (241593171 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162123197903 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162123197903 / 100000000000) = 1/(100000000000 / 162123197903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8017 : Bounds (483186341 / 1000000000) (241593171 / 500000000) (Real.log (162123197903 / 100000000000)) := by
  have h := reflection_log_8017_neg
  have he : Real.log (162123197903 / 100000000000) = -Real.log (100000000000 / 162123197903) := by
    rw [show ((162123197903 / 100000000000) : ℝ) = ((100000000000 / 162123197903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8018_neg : (96849197 / 200000000) ≤ -Real.log (500000000000 / 811475409837) ∧
    -Real.log (500000000000 / 811475409837) ≤ (242122993 / 500000000) := by
  have h := checkLog_sound (w := (311475409837 / 1311475409837)) (n := 12)
    (lo := (96849197 / 200000000)) (hi := (242122993 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((811475409837 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(811475409837 / 500000000000) = 1/(500000000000 / 811475409837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8018 : Bounds (96849197 / 200000000) (242122993 / 500000000) (Real.log (811475409837 / 500000000000)) := by
  have h := reflection_log_8018_neg
  have he : Real.log (811475409837 / 500000000000) = -Real.log (500000000000 / 811475409837) := by
    rw [show ((811475409837 / 500000000000) : ℝ) = ((500000000000 / 811475409837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8019_neg : (106748587 / 500000000) ≤ -Real.log (500 / 619) ∧
    -Real.log (500 / 619) ≤ (8539887 / 40000000) := by
  have h := checkLog_sound (w := (119 / 1119)) (n := 12)
    (lo := (106748587 / 500000000)) (hi := (8539887 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((619 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(619 / 500) = 1/(500 / 619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8019 : Bounds (106748587 / 500000000) (8539887 / 40000000) (Real.log (619 / 500)) := by
  have h := reflection_log_8019_neg
  have he : Real.log (619 / 500) = -Real.log (500 / 619) := by
    rw [show ((619 / 500) : ℝ) = ((500 / 619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8020_neg : (271808723 / 1000000000) ≤ -Real.log (381 / 500) ∧
    -Real.log (381 / 500) ≤ (67952181 / 250000000) := by
  have h := checkLog_sound (w := (119 / 881)) (n := 12)
    (lo := (271808723 / 1000000000)) (hi := (67952181 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 381) = 1/(381 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8020 : Bounds (-67952181 / 250000000) (-271808723 / 1000000000) (Real.log (381 / 500)) := by
  have h := reflection_log_8020_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8021_neg : (237971 / 1000000000) ≤ -Real.log (500000 / 500119) ∧
    -Real.log (500000 / 500119) ≤ (59493 / 250000000) := by
  have h := checkLog_sound (w := (119 / 1000119)) (n := 12)
    (lo := (237971 / 1000000000)) (hi := (59493 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500119 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500119 / 500000) = 1/(500000 / 500119) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8021 : Bounds (237971 / 1000000000) (59493 / 250000000) (Real.log (500119 / 500000)) := by
  have h := reflection_log_8021_neg
  have he : Real.log (500119 / 500000) = -Real.log (500000 / 500119) := by
    rw [show ((500119 / 500000) : ℝ) = ((500000 / 500119) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8022_neg : (59507 / 250000000) ≤ -Real.log (499881 / 500000) ∧
    -Real.log (499881 / 500000) ≤ (238029 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 999881)) (n := 12)
    (lo := (59507 / 250000000)) (hi := (238029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499881) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499881) = 1/(499881 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8022 : Bounds (-238029 / 1000000000) (-59507 / 250000000) (Real.log (499881 / 500000)) := by
  have h := reflection_log_8022_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8023_neg : (113203677 / 1000000000) ≤ -Real.log (50000 / 55993) ∧
    -Real.log (50000 / 55993) ≤ (56601839 / 500000000) := by
  have h := checkLog_sound (w := (5993 / 105993)) (n := 12)
    (lo := (113203677 / 1000000000)) (hi := (56601839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((55993 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(55993 / 50000) = 1/(50000 / 55993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8023 : Bounds (113203677 / 1000000000) (56601839 / 500000000) (Real.log (55993 / 50000)) := by
  have h := reflection_log_8023_neg
  have he : Real.log (55993 / 50000) = -Real.log (50000 / 55993) := by
    rw [show ((55993 / 50000) : ℝ) = ((50000 / 55993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8024_neg : (127674293 / 1000000000) ≤ -Real.log (44007 / 50000) ∧
    -Real.log (44007 / 50000) ≤ (63837147 / 500000000) := by
  have h := checkLog_sound (w := (5993 / 94007)) (n := 12)
    (lo := (127674293 / 1000000000)) (hi := (63837147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 44007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 44007) = 1/(44007 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8024 : Bounds (-63837147 / 500000000) (-127674293 / 1000000000) (Real.log (44007 / 50000)) := by
  have h := reflection_log_8024_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8025_neg : (56822353 / 500000000) ≤ -Real.log (500000 / 560177) ∧
    -Real.log (500000 / 560177) ≤ (113644707 / 1000000000) := by
  have h := checkLog_sound (w := (60177 / 1060177)) (n := 12)
    (lo := (56822353 / 500000000)) (hi := (113644707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((560177 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(560177 / 500000) = 1/(500000 / 560177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8025 : Bounds (56822353 / 500000000) (113644707 / 1000000000) (Real.log (560177 / 500000)) := by
  have h := reflection_log_8025_neg
  have he : Real.log (560177 / 500000) = -Real.log (500000 / 560177) := by
    rw [show ((560177 / 500000) : ℝ) = ((500000 / 560177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8026_neg : (5129429 / 40000000) ≤ -Real.log (439823 / 500000) ∧
    -Real.log (439823 / 500000) ≤ (64117863 / 500000000) := by
  have h := checkLog_sound (w := (60177 / 939823)) (n := 12)
    (lo := (5129429 / 40000000)) (hi := (64117863 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 439823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 439823) = 1/(439823 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8026 : Bounds (-64117863 / 500000000) (-5129429 / 40000000) (Real.log (439823 / 500000)) := by
  have h := reflection_log_8026_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8027_neg : (7295509 / 500000000) ≤ -Real.log (246378728671 / 250000000000) ∧
    -Real.log (246378728671 / 250000000000) ≤ (14591019 / 1000000000) := by
  have h := checkLog_sound (w := (3621271329 / 496378728671)) (n := 12)
    (lo := (7295509 / 500000000)) (hi := (14591019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246378728671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246378728671) = 1/(246378728671 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8027 : Bounds (-14591019 / 1000000000) (-7295509 / 500000000) (Real.log (246378728671 / 250000000000)) := by
  have h := reflection_log_8027_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8028_neg : (2894123 / 200000000) ≤ -Real.log (2464083951 / 2500000000) ∧
    -Real.log (2464083951 / 2500000000) ≤ (1808827 / 125000000) := by
  have h := checkLog_sound (w := (35916049 / 4964083951)) (n := 12)
    (lo := (2894123 / 200000000)) (hi := (1808827 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2464083951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2464083951) = 1/(2464083951 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8028 : Bounds (-1808827 / 125000000) (-2894123 / 200000000) (Real.log (2464083951 / 2500000000)) := by
  have h := reflection_log_8028_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8029_neg : (24087797 / 100000000) ≤ -Real.log (125000000000 / 159045719999) ∧
    -Real.log (125000000000 / 159045719999) ≤ (240877971 / 1000000000) := by
  have h := checkLog_sound (w := (34045719999 / 284045719999)) (n := 12)
    (lo := (24087797 / 100000000)) (hi := (240877971 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((159045719999 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(159045719999 / 125000000000) = 1/(125000000000 / 159045719999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8029 : Bounds (24087797 / 100000000) (240877971 / 1000000000) (Real.log (159045719999 / 125000000000)) := by
  have h := reflection_log_8029_neg
  have he : Real.log (159045719999 / 125000000000) = -Real.log (125000000000 / 159045719999) := by
    rw [show ((159045719999 / 125000000000) : ℝ) = ((125000000000 / 159045719999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8030_neg : (241880431 / 1000000000) ≤ -Real.log (500000000000 / 636820948427) ∧
    -Real.log (500000000000 / 636820948427) ≤ (15117527 / 62500000) := by
  have h := checkLog_sound (w := (136820948427 / 1136820948427)) (n := 12)
    (lo := (241880431 / 1000000000)) (hi := (15117527 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((636820948427 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(636820948427 / 500000000000) = 1/(500000000000 / 636820948427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8030 : Bounds (241880431 / 1000000000) (15117527 / 62500000) (Real.log (636820948427 / 500000000000)) := by
  have h := reflection_log_8030_neg
  have he : Real.log (636820948427 / 500000000000) = -Real.log (500000000000 / 636820948427) := by
    rw [show ((636820948427 / 500000000000) : ℝ) = ((500000000000 / 636820948427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8031_neg : (96849197 / 200000000) ≤ -Real.log (125000000000 / 202868852459) ∧
    -Real.log (125000000000 / 202868852459) ≤ (242122993 / 500000000) := by
  have h := checkLog_sound (w := (77868852459 / 327868852459)) (n := 12)
    (lo := (96849197 / 200000000)) (hi := (242122993 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((202868852459 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(202868852459 / 125000000000) = 1/(125000000000 / 202868852459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8031 : Bounds (96849197 / 200000000) (242122993 / 500000000) (Real.log (202868852459 / 125000000000)) := by
  have h := reflection_log_8031_neg
  have he : Real.log (202868852459 / 125000000000) = -Real.log (125000000000 / 202868852459) := by
    rw [show ((202868852459 / 125000000000) : ℝ) = ((125000000000 / 202868852459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8032_neg : (485305897 / 1000000000) ≤ -Real.log (250000000000 / 406167979003) ∧
    -Real.log (250000000000 / 406167979003) ≤ (242652949 / 500000000) := by
  have h := checkLog_sound (w := (156167979003 / 656167979003)) (n := 12)
    (lo := (485305897 / 1000000000)) (hi := (242652949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((406167979003 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(406167979003 / 250000000000) = 1/(250000000000 / 406167979003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8032 : Bounds (485305897 / 1000000000) (242652949 / 500000000) (Real.log (406167979003 / 250000000000)) := by
  have h := reflection_log_8032_neg
  have he : Real.log (406167979003 / 250000000000) = -Real.log (250000000000 / 406167979003) := by
    rw [show ((406167979003 / 250000000000) : ℝ) = ((250000000000 / 406167979003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8033_neg : (213900969 / 1000000000) ≤ -Real.log (2000 / 2477) ∧
    -Real.log (2000 / 2477) ≤ (21390097 / 100000000) := by
  have h := checkLog_sound (w := (477 / 4477)) (n := 12)
    (lo := (213900969 / 1000000000)) (hi := (21390097 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2477 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2477 / 2000) = 1/(2000 / 2477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8033 : Bounds (213900969 / 1000000000) (21390097 / 100000000) (Real.log (2477 / 2000)) := by
  have h := reflection_log_8033_neg
  have he : Real.log (2477 / 2000) = -Real.log (2000 / 2477) := by
    rw [show ((2477 / 2000) : ℝ) = ((2000 / 2477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8034_neg : (136232553 / 500000000) ≤ -Real.log (1523 / 2000) ∧
    -Real.log (1523 / 2000) ≤ (272465107 / 1000000000) := by
  have h := checkLog_sound (w := (477 / 3523)) (n := 12)
    (lo := (136232553 / 500000000)) (hi := (272465107 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1523) = 1/(1523 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8034 : Bounds (-272465107 / 1000000000) (-136232553 / 500000000) (Real.log (1523 / 2000)) := by
  have h := reflection_log_8034_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8035_neg : (238471 / 1000000000) ≤ -Real.log (2000000 / 2000477) ∧
    -Real.log (2000000 / 2000477) ≤ (29809 / 125000000) := by
  have h := checkLog_sound (w := (477 / 4000477)) (n := 12)
    (lo := (238471 / 1000000000)) (hi := (29809 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000477 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000477 / 2000000) = 1/(2000000 / 2000477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8035 : Bounds (238471 / 1000000000) (29809 / 125000000) (Real.log (2000477 / 2000000)) := by
  have h := reflection_log_8035_neg
  have he : Real.log (2000477 / 2000000) = -Real.log (2000000 / 2000477) := by
    rw [show ((2000477 / 2000000) : ℝ) = ((2000000 / 2000477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8036_neg : (3727 / 15625000) ≤ -Real.log (1999523 / 2000000) ∧
    -Real.log (1999523 / 2000000) ≤ (238529 / 1000000000) := by
  have h := checkLog_sound (w := (477 / 3999523)) (n := 12)
    (lo := (3727 / 15625000)) (hi := (238529 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999523) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999523) = 1/(1999523 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8036 : Bounds (-238529 / 1000000000) (-3727 / 15625000) (Real.log (1999523 / 2000000)) := by
  have h := reflection_log_8036_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8037_neg : (28358509 / 250000000) ≤ -Real.log (500000 / 560059) ∧
    -Real.log (500000 / 560059) ≤ (113434037 / 1000000000) := by
  have h := checkLog_sound (w := (60059 / 1060059)) (n := 12)
    (lo := (28358509 / 250000000)) (hi := (113434037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((560059 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(560059 / 500000) = 1/(500000 / 560059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8037 : Bounds (28358509 / 250000000) (113434037 / 1000000000) (Real.log (560059 / 500000)) := by
  have h := reflection_log_8037_neg
  have he : Real.log (560059 / 500000) = -Real.log (500000 / 560059) := by
    rw [show ((560059 / 500000) : ℝ) = ((500000 / 560059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8038_neg : (127967471 / 1000000000) ≤ -Real.log (439941 / 500000) ∧
    -Real.log (439941 / 500000) ≤ (7997967 / 62500000) := by
  have h := checkLog_sound (w := (60059 / 939941)) (n := 12)
    (lo := (127967471 / 1000000000)) (hi := (7997967 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 439941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 439941) = 1/(439941 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8038 : Bounds (-7997967 / 62500000) (-127967471 / 1000000000) (Real.log (439941 / 500000)) := by
  have h := reflection_log_8038_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8039_neg : (113875857 / 1000000000) ≤ -Real.log (1000000 / 1120613) ∧
    -Real.log (1000000 / 1120613) ≤ (56937929 / 500000000) := by
  have h := checkLog_sound (w := (120613 / 2120613)) (n := 12)
    (lo := (113875857 / 1000000000)) (hi := (56937929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1120613 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1120613 / 1000000) = 1/(1000000 / 1120613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8039 : Bounds (113875857 / 1000000000) (56937929 / 500000000) (Real.log (1120613 / 1000000)) := by
  have h := reflection_log_8039_neg
  have he : Real.log (1120613 / 1000000) = -Real.log (1000000 / 1120613) := by
    rw [show ((1120613 / 1000000) : ℝ) = ((1000000 / 1120613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8040_neg : (25706041 / 200000000) ≤ -Real.log (879387 / 1000000) ∧
    -Real.log (879387 / 1000000) ≤ (64265103 / 500000000) := by
  have h := checkLog_sound (w := (120613 / 1879387)) (n := 12)
    (lo := (25706041 / 200000000)) (hi := (64265103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 879387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 879387) = 1/(879387 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8040 : Bounds (-64265103 / 500000000) (-25706041 / 200000000) (Real.log (879387 / 1000000)) := by
  have h := reflection_log_8040_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8041_neg : (3663587 / 250000000) ≤ -Real.log (985452504231 / 1000000000000) ∧
    -Real.log (985452504231 / 1000000000000) ≤ (14654349 / 1000000000) := by
  have h := checkLog_sound (w := (14547495769 / 1985452504231)) (n := 12)
    (lo := (3663587 / 250000000)) (hi := (14654349 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 985452504231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 985452504231) = 1/(985452504231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8041 : Bounds (-14654349 / 1000000000) (-3663587 / 250000000) (Real.log (985452504231 / 1000000000000)) := by
  have h := reflection_log_8041_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8042_neg : (7266717 / 500000000) ≤ -Real.log (246392916519 / 250000000000) ∧
    -Real.log (246392916519 / 250000000000) ≤ (2906687 / 200000000) := by
  have h := checkLog_sound (w := (3607083481 / 496392916519)) (n := 12)
    (lo := (7266717 / 500000000)) (hi := (2906687 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 246392916519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 246392916519) = 1/(246392916519 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8042 : Bounds (-2906687 / 200000000) (-7266717 / 500000000) (Real.log (246392916519 / 250000000000)) := by
  have h := reflection_log_8042_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8043_neg : (60350377 / 250000000) ≤ -Real.log (500000000000 / 636516032831) ∧
    -Real.log (500000000000 / 636516032831) ≤ (241401509 / 1000000000) := by
  have h := checkLog_sound (w := (136516032831 / 1136516032831)) (n := 12)
    (lo := (60350377 / 250000000)) (hi := (241401509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((636516032831 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(636516032831 / 500000000000) = 1/(500000000000 / 636516032831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8043 : Bounds (60350377 / 250000000) (241401509 / 1000000000) (Real.log (636516032831 / 500000000000)) := by
  have h := reflection_log_8043_neg
  have he : Real.log (636516032831 / 500000000000) = -Real.log (500000000000 / 636516032831) := by
    rw [show ((636516032831 / 500000000000) : ℝ) = ((500000000000 / 636516032831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8044_neg : (121203031 / 500000000) ≤ -Real.log (100000000000 / 127431153747) ∧
    -Real.log (100000000000 / 127431153747) ≤ (242406063 / 1000000000) := by
  have h := checkLog_sound (w := (27431153747 / 227431153747)) (n := 12)
    (lo := (121203031 / 500000000)) (hi := (242406063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127431153747 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(127431153747 / 100000000000) = 1/(100000000000 / 127431153747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8044 : Bounds (121203031 / 500000000) (242406063 / 1000000000) (Real.log (127431153747 / 100000000000)) := by
  have h := reflection_log_8044_neg
  have he : Real.log (127431153747 / 100000000000) = -Real.log (100000000000 / 127431153747) := by
    rw [show ((127431153747 / 100000000000) : ℝ) = ((100000000000 / 127431153747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8045_neg : (485305897 / 1000000000) ≤ -Real.log (100000000000 / 162467191601) ∧
    -Real.log (100000000000 / 162467191601) ≤ (242652949 / 500000000) := by
  have h := checkLog_sound (w := (62467191601 / 262467191601)) (n := 12)
    (lo := (485305897 / 1000000000)) (hi := (242652949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162467191601 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162467191601 / 100000000000) = 1/(100000000000 / 162467191601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8045 : Bounds (485305897 / 1000000000) (242652949 / 500000000) (Real.log (162467191601 / 100000000000)) := by
  have h := reflection_log_8045_neg
  have he : Real.log (162467191601 / 100000000000) = -Real.log (100000000000 / 162467191601) := by
    rw [show ((162467191601 / 100000000000) : ℝ) = ((100000000000 / 162467191601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8046_neg : (121591519 / 250000000) ≤ -Real.log (100000000000 / 162639527249) ∧
    -Real.log (100000000000 / 162639527249) ≤ (486366077 / 1000000000) := by
  have h := checkLog_sound (w := (62639527249 / 262639527249)) (n := 12)
    (lo := (121591519 / 250000000)) (hi := (486366077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((162639527249 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(162639527249 / 100000000000) = 1/(100000000000 / 162639527249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8046 : Bounds (121591519 / 250000000) (486366077 / 1000000000) (Real.log (162639527249 / 100000000000)) := by
  have h := reflection_log_8046_neg
  have he : Real.log (162639527249 / 100000000000) = -Real.log (100000000000 / 162639527249) := by
    rw [show ((162639527249 / 100000000000) : ℝ) = ((100000000000 / 162639527249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8047_neg : (107152301 / 500000000) ≤ -Real.log (1000 / 1239) ∧
    -Real.log (1000 / 1239) ≤ (214304603 / 1000000000) := by
  have h := checkLog_sound (w := (239 / 2239)) (n := 12)
    (lo := (107152301 / 500000000)) (hi := (214304603 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1239 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1239 / 1000) = 1/(1000 / 1239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8047 : Bounds (107152301 / 500000000) (214304603 / 1000000000) (Real.log (1239 / 1000)) := by
  have h := reflection_log_8047_neg
  have he : Real.log (1239 / 1000) = -Real.log (1000 / 1239) := by
    rw [show ((1239 / 1000) : ℝ) = ((1000 / 1239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8048_neg : (273121921 / 1000000000) ≤ -Real.log (761 / 1000) ∧
    -Real.log (761 / 1000) ≤ (136560961 / 500000000) := by
  have h := checkLog_sound (w := (239 / 1761)) (n := 12)
    (lo := (273121921 / 1000000000)) (hi := (136560961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 761) = 1/(761 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8048 : Bounds (-136560961 / 500000000) (-273121921 / 1000000000) (Real.log (761 / 1000)) := by
  have h := reflection_log_8048_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8049_neg : (238971 / 1000000000) ≤ -Real.log (1000000 / 1000239) ∧
    -Real.log (1000000 / 1000239) ≤ (59743 / 250000000) := by
  have h := checkLog_sound (w := (239 / 2000239)) (n := 12)
    (lo := (238971 / 1000000000)) (hi := (59743 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000239 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000239 / 1000000) = 1/(1000000 / 1000239) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8049 : Bounds (238971 / 1000000000) (59743 / 250000000) (Real.log (1000239 / 1000000)) := by
  have h := reflection_log_8049_neg
  have he : Real.log (1000239 / 1000000) = -Real.log (1000000 / 1000239) := by
    rw [show ((1000239 / 1000000) : ℝ) = ((1000000 / 1000239) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8050_neg : (59757 / 250000000) ≤ -Real.log (999761 / 1000000) ∧
    -Real.log (999761 / 1000000) ≤ (239029 / 1000000000) := by
  have h := checkLog_sound (w := (239 / 1999761)) (n := 12)
    (lo := (59757 / 250000000)) (hi := (239029 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999761) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999761) = 1/(999761 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8050 : Bounds (-239029 / 1000000000) (-59757 / 250000000) (Real.log (999761 / 1000000)) := by
  have h := reflection_log_8050_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8051_neg : (113664343 / 1000000000) ≤ -Real.log (125000 / 140047) ∧
    -Real.log (125000 / 140047) ≤ (14208043 / 125000000) := by
  have h := checkLog_sound (w := (15047 / 265047)) (n := 12)
    (lo := (113664343 / 1000000000)) (hi := (14208043 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((140047 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(140047 / 125000) = 1/(125000 / 140047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8051 : Bounds (113664343 / 1000000000) (14208043 / 125000000) (Real.log (140047 / 125000)) := by
  have h := reflection_log_8051_neg
  have he : Real.log (140047 / 125000) = -Real.log (125000 / 140047) := by
    rw [show ((140047 / 125000) : ℝ) = ((125000 / 140047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8052_neg : (25652147 / 200000000) ≤ -Real.log (109953 / 125000) ∧
    -Real.log (109953 / 125000) ≤ (1002037 / 7812500) := by
  have h := checkLog_sound (w := (15047 / 234953)) (n := 12)
    (lo := (25652147 / 200000000)) (hi := (1002037 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 109953) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 109953) = 1/(109953 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8052 : Bounds (-1002037 / 7812500) (-25652147 / 200000000) (Real.log (109953 / 125000)) := by
  have h := reflection_log_8052_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8053_neg : (114106061 / 1000000000) ≤ -Real.log (1000000 / 1120871) ∧
    -Real.log (1000000 / 1120871) ≤ (57053031 / 500000000) := by
  have h := checkLog_sound (w := (120871 / 2120871)) (n := 12)
    (lo := (114106061 / 1000000000)) (hi := (57053031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1120871 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1120871 / 1000000) = 1/(1000000 / 1120871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8053 : Bounds (114106061 / 1000000000) (57053031 / 500000000) (Real.log (1120871 / 1000000)) := by
  have h := reflection_log_8053_neg
  have he : Real.log (1120871 / 1000000) = -Real.log (1000000 / 1120871) := by
    rw [show ((1120871 / 1000000) : ℝ) = ((1000000 / 1120871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8054_neg : (64411817 / 500000000) ≤ -Real.log (879129 / 1000000) ∧
    -Real.log (879129 / 1000000) ≤ (25764727 / 200000000) := by
  have h := checkLog_sound (w := (120871 / 1879129)) (n := 12)
    (lo := (64411817 / 500000000)) (hi := (25764727 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 879129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 879129) = 1/(879129 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8054 : Bounds (-25764727 / 200000000) (-64411817 / 500000000) (Real.log (879129 / 1000000)) := by
  have h := reflection_log_8054_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8055_neg : (3679393 / 250000000) ≤ -Real.log (985390201359 / 1000000000000) ∧
    -Real.log (985390201359 / 1000000000000) ≤ (14717573 / 1000000000) := by
  have h := checkLog_sound (w := (14609798641 / 1985390201359)) (n := 12)
    (lo := (3679393 / 250000000)) (hi := (14717573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 985390201359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 985390201359) = 1/(985390201359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8055 : Bounds (-14717573 / 1000000000) (-3679393 / 250000000) (Real.log (985390201359 / 1000000000000)) := by
  have h := reflection_log_8055_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8056_neg : (1824549 / 125000000) ≤ -Real.log (15398587791 / 15625000000) ∧
    -Real.log (15398587791 / 15625000000) ≤ (14596393 / 1000000000) := by
  have h := checkLog_sound (w := (226412209 / 31023587791)) (n := 12)
    (lo := (1824549 / 125000000)) (hi := (14596393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15398587791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15398587791) = 1/(15398587791 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8056 : Bounds (-14596393 / 1000000000) (-1824549 / 125000000) (Real.log (15398587791 / 15625000000)) := by
  have h := reflection_log_8056_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8057_neg : (120962539 / 500000000) ≤ -Real.log (500000000000 / 636849381099) ∧
    -Real.log (500000000000 / 636849381099) ≤ (241925079 / 1000000000) := by
  have h := checkLog_sound (w := (136849381099 / 1136849381099)) (n := 12)
    (lo := (120962539 / 500000000)) (hi := (241925079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((636849381099 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(636849381099 / 500000000000) = 1/(500000000000 / 636849381099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8057 : Bounds (120962539 / 500000000) (241925079 / 1000000000) (Real.log (636849381099 / 500000000000)) := by
  have h := reflection_log_8057_neg
  have he : Real.log (636849381099 / 500000000000) = -Real.log (500000000000 / 636849381099) := by
    rw [show ((636849381099 / 500000000000) : ℝ) = ((500000000000 / 636849381099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8058_neg : (7591553 / 31250000) ≤ -Real.log (500000000000 / 637489492441) ∧
    -Real.log (500000000000 / 637489492441) ≤ (242929697 / 1000000000) := by
  have h := checkLog_sound (w := (137489492441 / 1137489492441)) (n := 12)
    (lo := (7591553 / 31250000)) (hi := (242929697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((637489492441 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(637489492441 / 500000000000) = 1/(500000000000 / 637489492441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8058 : Bounds (7591553 / 31250000) (242929697 / 1000000000) (Real.log (637489492441 / 500000000000)) := by
  have h := reflection_log_8058_neg
  have he : Real.log (637489492441 / 500000000000) = -Real.log (500000000000 / 637489492441) := by
    rw [show ((637489492441 / 500000000000) : ℝ) = ((500000000000 / 637489492441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8059_neg : (121591519 / 250000000) ≤ -Real.log (125000000000 / 203299409061) ∧
    -Real.log (125000000000 / 203299409061) ≤ (486366077 / 1000000000) := by
  have h := checkLog_sound (w := (78299409061 / 328299409061)) (n := 12)
    (lo := (121591519 / 250000000)) (hi := (486366077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((203299409061 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(203299409061 / 125000000000) = 1/(125000000000 / 203299409061) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8059 : Bounds (121591519 / 250000000) (486366077 / 1000000000) (Real.log (203299409061 / 125000000000)) := by
  have h := reflection_log_8059_neg
  have he : Real.log (203299409061 / 125000000000) = -Real.log (125000000000 / 203299409061) := by
    rw [show ((203299409061 / 125000000000) : ℝ) = ((125000000000 / 203299409061) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8060_neg : (487426523 / 1000000000) ≤ -Real.log (500000000000 / 814060446781) ∧
    -Real.log (500000000000 / 814060446781) ≤ (121856631 / 250000000) := by
  have h := checkLog_sound (w := (314060446781 / 1314060446781)) (n := 12)
    (lo := (487426523 / 1000000000)) (hi := (121856631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((814060446781 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(814060446781 / 500000000000) = 1/(500000000000 / 814060446781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8060 : Bounds (487426523 / 1000000000) (121856631 / 250000000) (Real.log (814060446781 / 500000000000)) := by
  have h := reflection_log_8060_neg
  have he : Real.log (814060446781 / 500000000000) = -Real.log (500000000000 / 814060446781) := by
    rw [show ((814060446781 / 500000000000) : ℝ) = ((500000000000 / 814060446781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8061_neg : (26838509 / 125000000) ≤ -Real.log (2000 / 2479) ∧
    -Real.log (2000 / 2479) ≤ (214708073 / 1000000000) := by
  have h := checkLog_sound (w := (479 / 4479)) (n := 12)
    (lo := (26838509 / 125000000)) (hi := (214708073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2479 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2479 / 2000) = 1/(2000 / 2479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8061 : Bounds (26838509 / 125000000) (214708073 / 1000000000) (Real.log (2479 / 2000)) := by
  have h := reflection_log_8061_neg
  have he : Real.log (2479 / 2000) = -Real.log (2000 / 2479) := by
    rw [show ((2479 / 2000) : ℝ) = ((2000 / 2479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8062_neg : (273779167 / 1000000000) ≤ -Real.log (1521 / 2000) ∧
    -Real.log (1521 / 2000) ≤ (8555599 / 31250000) := by
  have h := checkLog_sound (w := (479 / 3521)) (n := 12)
    (lo := (273779167 / 1000000000)) (hi := (8555599 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1521) = 1/(1521 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8062 : Bounds (-8555599 / 31250000) (-273779167 / 1000000000) (Real.log (1521 / 2000)) := by
  have h := reflection_log_8062_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_8063_neg : (239471 / 1000000000) ≤ -Real.log (2000000 / 2000479) ∧
    -Real.log (2000000 / 2000479) ≤ (14967 / 62500000) := by
  have h := checkLog_sound (w := (479 / 4000479)) (n := 12)
    (lo := (239471 / 1000000000)) (hi := (14967 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000479 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000479 / 2000000) = 1/(2000000 / 2000479) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8063 : Bounds (239471 / 1000000000) (14967 / 62500000) (Real.log (2000479 / 2000000)) := by
  have h := reflection_log_8063_neg
  have he : Real.log (2000479 / 2000000) = -Real.log (2000000 / 2000479) := by
    rw [show ((2000479 / 2000000) : ℝ) = ((2000000 / 2000479) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily
